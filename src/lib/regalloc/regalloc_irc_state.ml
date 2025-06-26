open Core
open Regular.Std
open Pseudo

module Lset = Label.Tree_set

let reduce a b = match a, b with
  | (#Type.imm as ia), (#Type.imm as ib)
    when Type.sizeof_imm ia < Type.sizeof_imm ib -> b
  | #Type.imm, #Type.imm -> a
  | (#Type.fp as fa), (#Type.fp as fb)
    when Type.sizeof_fp fa < Type.sizeof_fp fb -> b
  | #Type.fp, #Type.fp -> a
  | `v128, `v128 -> `v128
  | _ -> assert false

module Make(M : Machine_intf.S) = struct
  module Rv = M.Regvar
  module Regs = Regalloc_regs.Make(M)
  module Live = Pseudo_passes.Live(M)

  (* Terminology:

     - [simplifyWorklist]: list of low-degree non-move-related nodes
     - [freezeWorklist]: low-degree move-related nodes
     - [spillWorklist]: high-degree nodes
     - [spilledNodes]: nodes marked for spilling during this round; initially empty
     - [coalescedNodes]: registers that have been coalesced; when the move u:=v is
       coalesced, one of u or v is added to this set, and the other is put back on
       some worklist
     - [coloredNodes]: nodes successfully colored
     - [selectStack]: stack containing temporaries removed from the graph
     - [coalescedMoves]: moves that have been coalesced
     - [constrainedMoves]: moves whose source and target interfere
     - [frozenMoves]: moves that will no longer be considered for coalescing
     - [worklistMoves]: moves enabled for possible coalescing
     - [activeMoves]: moves not yet ready for coalescing
  *)
  type t = {
    mutable fn      : (M.Insn.t, M.Reg.t) func;
    adjlist         : Rv.Set.t Rv.Table.t;
    degree          : int Rv.Table.t;
    moves           : Lset.t Rv.Table.t;
    copies          : (Rv.t * Rv.t) Label.Table.t;
    mutable wmoves  : Lset.t; (* worklist moves *)
    mutable amoves  : Lset.t; (* active moves *)
    mutable cmoves  : Lset.t; (* coalesced moves *)
    mutable kmoves  : Lset.t; (* constrained moves *)
    mutable fmoves  : Lset.t; (* frozen moves *)
    wspill          : Rv.Hash_set.t;
    wfreeze         : Rv.Hash_set.t;
    wsimplify       : Rv.Hash_set.t;
    coalesced       : Rv.Hash_set.t;
    mutable spilled : Rv.Set.t;
    colored         : Rv.Hash_set.t;
    initial         : Rv.Hash_set.t;
    slots           : Rv.Hash_set.t;
    colors          : int Rv.Table.t;
    select          : Rv.t Stack.t;
    alias           : Rv.t Rv.Table.t;
    keep            : Rv.Set.t;
    mutable types   : [Type.basic | `v128] Rv.Map.t;
  } [@@ocaml.warning "-69"]

  (* Set of registers that should always be live at the exit. *)
  let init_keep fn =
    let init = Rv.Set.singleton @@ Rv.reg M.Reg.sp in
    Func.rets fn |> Seq.map ~f:Rv.reg |> Seq.fold ~init ~f:Set.add

  let create fn = {
    fn;
    adjlist = Rv.Table.create ();
    degree = Rv.Table.create ();
    moves = Rv.Table.create ();
    copies = Label.Table.create ();
    wmoves = Lset.empty;
    amoves = Lset.empty;
    cmoves = Lset.empty;
    kmoves = Lset.empty;
    fmoves = Lset.empty;
    wspill = Rv.Hash_set.create ();
    wfreeze = Rv.Hash_set.create ();
    wsimplify = Rv.Hash_set.create ();
    coalesced = Rv.Hash_set.create ();
    spilled = Rv.Set.empty;
    colored = Rv.Hash_set.create ();
    initial = Rv.Hash_set.create ();
    slots = Rv.Hash_set.create ();
    colors = Rv.Table.create ();
    select = Stack.create ();
    alias = Rv.Table.create ();
    keep = init_keep fn;
    types = Rv.Map.empty;
  }

  (* Explicit registers and variables that correspond to stack slots
     should be excluded from consideration. *)
  let exclude_from_coloring t n = Rv.is_reg n || Hash_set.mem t.slots n
  let can_be_colored t n = not @@ exclude_from_coloring t n

  let inc_degree t n =
    Hashtbl.update t.degree n ~f:(function
        | Some d -> d + 1
        | None -> 1)

  let dec_degree t n =
    Hashtbl.update t.degree n ~f:(function
        | Some d -> max 0 (d - 1)
        | None -> 0)

  let degree' t n = Hashtbl.find t.degree n

  (* All variables should be in this table. Preassigned registers
     won't be in here, so they should just get the maximum value. *)
  let degree t n = degree' t n |> Option.value ~default:Int.max_value

  (* NB: we include nodes that could be pre-colored as keys here. *)
  let add_adjlist t u v =
    Hashtbl.update t.adjlist u ~f:(function
        | None -> Rv.Set.singleton v
        | Some s -> Set.add s v)

  (* NB: this is unidirectional *)
  let has_edge t u v = match Hashtbl.find t.adjlist u with
    | Some s -> Set.mem s v
    | None -> false

  (* NB: since we include nodes that can be precolored as keys, we need
     to exclude them here. *)
  let adjlist t n =
    let default = Rv.Set.empty in
    if can_be_colored t n
    then Hashtbl.find t.adjlist n |> Option.value ~default
    else default

  (* adjList[n] \ (selectStack U coalescedNodes) *)
  let adjacent t n =
    let a = adjlist t n in
    if not @@ Set.is_empty a then
      let a = Stack.fold t.select ~init:a ~f:Set.remove in
      Hash_set.fold t.coalesced ~init:a ~f:Set.remove
    else a

  let moves t n = match Hashtbl.find t.moves n with
    | None -> Lset.empty
    | Some m -> m

  (* moveList[n] ^ (activeMoves U worklistMoves) *)
  let node_moves t n =
    Lset.inter (moves t n) (Lset.union t.amoves t.wmoves)

  (* NodeMoves(n) /= {} *)
  let move_related t n =
    not @@ Lset.is_empty @@ node_moves t n

  (* if n \in coalescedNodes then
       GetAlias(alias[n])
     else n *)
  let rec alias t n =
    if Hash_set.mem t.coalesced n
    then alias t @@ Hashtbl.find_exn t.alias n
    else n

  let color t n = match Rv.which n with
    | Second _ -> Hashtbl.find t.colors n
    | First r -> Regs.reg_color r

  let set_color t n c = Hashtbl.set t.colors ~key:n ~data:c

  let add_move t label n =
    Hashtbl.update t.moves n ~f:(function
        | None -> Lset.singleton label
        | Some ls -> Lset.add ls label)

  let add_initial t n =
    if can_be_colored t n then Hash_set.add t.initial n

  let update_types t insn =
    let types = M.Regalloc.writes_with_types insn in
    t.types <- Map.merge_skewed t.types types ~combine:(fun ~key:_  -> reduce)

  (* initial: temporary registers, not preassigned a color and not yet
     processed by the algorithm. *)
  let init_initial t =
    Func.blks t.fn |> Seq.iter ~f:(fun b ->
        Blk.insns b |> Seq.iter ~f:(fun i ->
            let insn = Insn.insn i in
            let use = M.Insn.reads insn in
            let def = M.Insn.writes insn in
            Set.iter use ~f:(add_initial t);
            Set.iter def ~f:(add_initial t);
            update_types t insn))
end
