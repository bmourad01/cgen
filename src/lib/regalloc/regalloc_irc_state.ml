open Core
open Regular.Std
open Pseudo

module Lset = Label.Tree_set
module Id = Int

type id = Id.t

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
  module Loop = Loops.Make(Cfg)

  type copy = {
    dst  : id;
    src  : id;
    loop : int;
  }

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
    mutable fn          : (M.Insn.t, M.Reg.t) func;
    rv2id               : id Rv.Table.t;  (* regvar to interned ID *)
    id2rv               : Rv.t Vec.t;     (* interned ID to regvar *)
    mutable wsimplify   : Bitset.t;       (* simplify worklist *)
    mutable wfreeze     : Bitset.t;       (* freeze worklist *)
    mutable coalesced   : Bitset.t;       (* coalesced nodes *)
    mutable colored     : Bitset.t;       (* colored nodes *)
    mutable initial     : Bitset.t;       (* nodes not yet on a worklist *)
    mutable spilled     : Bitset.t;       (* spilled nodes *)
    mutable keep        : Rv.Set.t;       (* nodes that are live at the exits *)
    mutable reg_bits    : Bitset.t;       (* IDs that are pre-colored regs *)
    mutable slot_bits   : Bitset.t;       (* IDs that are stack-slot nodes *)
    mutable wmoves      : Lset.t;         (* worklist moves *)
    mutable amoves      : Lset.t;         (* active moves *)
    mutable cmoves      : Lset.t;         (* coalesced moves *)
    mutable kmoves      : Lset.t;         (* constrained moves *)
    mutable fmoves      : Lset.t;         (* frozen moves *)
    degree              : int array ref;  (* Int.max_value = not yet seen *)
    spill_cost          : int array ref;  (* estimated spill cost of each node *)
    mutable adjlist     : Bitset.t array; (* adjacency list of the interference graph *)
    mutable nuse        : int array;      (* use count for each node *)
    mutable colors      : int array;      (* node colors, -1 = not yet colored *)
    mutable alias       : id array;       (* node aliases (from combine/coalesce) *)
    mutable node_moves  : Lset.t array;   (* move instructions for each node *)
    mutable defs        : Lset.t array;   (* definition instructions for each node *)
    wspill              : id Pairing_heap.t;
    mutable wspill_elts : id Pairing_heap.Elt.t Option_array.t;
    select              : id Stack.t;
    copies              : copy Label.Table.t;
    insn_blks           : (Label.t * id) Label.Table.t;
    slots               : Rv.t Rv.Table.t;
    mutable types       : [Type.basic | `v128] Rv.Map.t;
    cfg                 : Pseudo.Cfg.t;
    loop                : Loop.t;
    dom                 : Label.t Semi_nca.tree;
    mutable live        : Live.t option;
  }

  let intern t rv =
    match Hashtbl.find t.rv2id rv with
    | Some id -> id
    | None ->
      let id = Vec.length t.id2rv in
      Hashtbl.set t.rv2id ~key:rv ~data:id;
      Vec.push t.id2rv rv;
      id

  let (.$[]) t rv = Hashtbl.find_exn t.rv2id rv
  let (.![]) t id = Vec.get_exn t.id2rv id

  let num_nodes t = Vec.length t.id2rv

  let alloc_arrays t =
    let n = num_nodes t in
    t.degree := Array.create ~len:n Int.max_value;
    t.spill_cost := Array.create ~len:n 0;
    t.adjlist <- Array.create ~len:n Bitset.empty;
    t.nuse <- Array.create ~len:n 0;
    t.colors <- Array.create ~len:n (-1);
    t.alias <- Array.init n ~f:Fn.id;
    t.node_moves <- Array.create ~len:n Lset.empty;
    t.defs <- Array.create ~len:n Lset.empty;
    t.wspill_elts <- Option_array.create ~len:n

  (* Explicit registers and variables that correspond to stack slots should
     be excluded from consideration. *)
  let exclude_from_coloring t id =
    Bitset.mem t.reg_bits id || Bitset.mem t.slot_bits id

  let can_be_colored t id = not (exclude_from_coloring t id)

  let degree' t id =
    let d = !(t.degree).(id) in
    if d = Int.max_value then None else Some d

  let degree t id = !(t.degree).(id)

  let ensure_degree t id =
    if can_be_colored t id then
      let arr = !(t.degree) in
      if arr.(id) = Int.max_value then arr.(id) <- 0

  let wspill_elt t id = Option_array.get t.wspill_elts id
  let has_wspill_elt t id = Option_array.is_some t.wspill_elts id
  let set_wspill_elt t id elt = Option_array.set_some t.wspill_elts id elt
  let clear_wspill_elt t id = Option_array.set_none t.wspill_elts id

  let add_spill t id =
    if can_be_colored t id && not (has_wspill_elt t id) then
      let () = Logs.debug (fun m ->
          m "%s: adding %a to spill worklist%!"
            __FUNCTION__ Rv.pp t.![id]) in
      let elt = Pairing_heap.add_removable t.wspill id in
      set_wspill_elt t id elt

  let remove_spill t id =
    wspill_elt t id |> Option.iter ~f:(fun elt ->
        Pairing_heap.remove t.wspill elt;
        clear_wspill_elt t id)

  let update_spill t id =
    wspill_elt t id |> Option.iter ~f:(fun elt ->
        let elt' = Pairing_heap.update t.wspill elt id in
        set_wspill_elt t id elt')

  let inc_degree t id =
    let arr = !(t.degree) in
    arr.(id) <- arr.(id) + 1;
    update_spill t id

  let dec_degree t id =
    let arr = !(t.degree) in
    arr.(id) <- max 0 (arr.(id) - 1);
    update_spill t id

  (* NB: we include nodes that could be pre-colored as keys here. *)
  let add_adjlist t u v =
    t.adjlist.(u) <- Bitset.set t.adjlist.(u) v

  (* NB: this is unidirectional *)
  let has_edge t u v = Bitset.mem t.adjlist.(u) v

  (* NB: since we include nodes that can be precolored as keys, we need to
     exclude them here. *)
  let adjlist t id =
    if can_be_colored t id
    then t.adjlist.(id)
    else Bitset.empty

  (* adjList[n] ∖ (selectStack ∪ coalescedNodes) *)
  let adjacent t id =
    let a = adjlist t id in
    if Bitset.is_empty a then a else
      let removed = Stack.fold t.select ~init:t.coalesced ~f:Bitset.set in
      Bitset.diff a removed

  let moves t id = t.node_moves.(id)

  (* moveList[n] ∩ (activeMoves ∪ worklistMoves) *)
  let node_moves t id =
    Lset.inter (moves t id) (Lset.union t.amoves t.wmoves)

  let move_related t id = not (Lset.is_empty (node_moves t id))

  let add_move t label id =
    t.node_moves.(id) <- Lset.add t.node_moves.(id) label

  let inc_use t id = t.nuse.(id) <- t.nuse.(id) + 1
  let num_uses t id = t.nuse.(id)

  let add_def t id label =
    t.defs.(id) <- Lset.add t.defs.(id) label

  (* if n ∈ coalescedNodes then GetAlias(alias[n]) else n *)
  let rec alias t id =
    if Bitset.mem t.coalesced id
    then alias t t.alias.(id)
    else id

  let color t id = match Rv.which t.![id] with
    | First r -> Regs.reg_color r
    | Second _ ->
      let c = t.colors.(id) in
      Option.some_if (c <> -1) c

  let set_color t id c =
    Logs.debug (fun m ->
        m "%s: assigning color %a=%d%!"
          __FUNCTION__ Rv.pp t.![id] c);
    t.colors.(id) <- c

  let add_initial t rv =
    let id = intern t rv in
    if can_be_colored t id then
      t.initial <- Bitset.set t.initial id

  let update_types t insn =
    let types = M.Regalloc.writes_with_types insn in
    t.types <- Map.merge_skewed t.types types ~combine:(fun ~key:_ -> reduce)

  let is_phi_var t id =
    match Rv.which t.![id] with
    | First _ -> false
    | Second (v, _) ->
      match Dict.find (Func.dict t.fn) Tags.phi_var with
      | None -> false
      | Some p -> Set.mem p v

  let weighted_spill_cost loop_depth = Int.pow 10 loop_depth

  let update_cost ?(factor = 1) ~loop_depth t id =
    if can_be_colored t id then
      let w = weighted_spill_cost loop_depth * factor in
      let arr = !(t.spill_cost) in
      arr.(id) <- arr.(id) + w

  (* cost(v) = (Σ_{u ∈ uses(v)} weight(u)) / degree(v)

     Here, the weighted cost of a use is 10^loop_depth(u).
  *)
  let spill_cost_float spill_arr degree_arr id =
    let d = (!degree_arr).(id) in
    if d = 0 || d = Int.max_value then Float.infinity else
      let cost = (!spill_arr).(id) in
      Int.to_float cost /. Int.to_float d

  let spill_cmp spill_arr degree_arr a b =
    Float.compare
      (spill_cost_float spill_arr degree_arr a)
      (spill_cost_float spill_arr degree_arr b)

  let create fn =
    let cfg = Pseudo.Cfg.create fn
        ~is_barrier:M.Insn.is_barrier
        ~dests:M.Insn.dests in
    let dom = Semi_nca.compute (module Pseudo.Cfg) cfg Label.pseudoentry in
    let loop = Loop.analyze ~dom ~name:(Pseudo.Func.name fn) cfg in
    let degree = ref @@ Array.create ~len:0 0 in
    let spill_cost = ref @@ Array.create ~len:0 0 in
    let wspill = Pairing_heap.create ~cmp:(spill_cmp spill_cost degree) () in {
      fn;
      rv2id = Rv.Table.create ();
      id2rv = Vec.create ();
      wsimplify = Bitset.empty;
      wfreeze = Bitset.empty;
      coalesced = Bitset.empty;
      colored = Bitset.empty;
      initial = Bitset.empty;
      spilled = Bitset.empty;
      keep = Rv.Set.empty;
      reg_bits = Bitset.empty;
      slot_bits = Bitset.empty;
      wmoves = Lset.empty;
      amoves = Lset.empty;
      cmoves = Lset.empty;
      kmoves = Lset.empty;
      fmoves = Lset.empty;
      degree;
      spill_cost;
      adjlist = [||];
      nuse = [||];
      colors = [||];
      alias = [||];
      node_moves = [||];
      defs = [||];
      wspill;
      wspill_elts = Option_array.empty;
      select = Stack.create ();
      copies = Label.Table.create ();
      insn_blks = Label.Table.create ();
      slots = Rv.Table.create ();
      types = Rv.Map.empty;
      cfg;
      loop;
      dom;
      live = None;
    }

  (* Before we can populate the `initial` set, we have to intern all
     of the regvars in the function. This should only happen once
     at startup. Newly introduced spill temporaries will be lazily
     interned for the next round. *)
  let init_initial_intern t =
    Func.blks t.fn |> Seq.iter ~f:(fun b ->
        Blk.insns b |> Seq.iter ~f:(fun i ->
            let insn = Insn.insn i in
            let f rv = ignore @@ intern t rv in
            M.Insn.reads insn |> Set.iter ~f;
            M.Insn.writes insn |> Set.iter ~f;
            update_types t insn));
    let sp = Rv.reg M.Reg.sp in
    t.keep <- Set.add t.keep sp;
    t.reg_bits <- Bitset.set t.reg_bits (intern t sp);
    Func.rets t.fn |> Seq.iter ~f:(fun r ->
        let rv = Rv.reg r in
        let id = intern t rv in
        t.keep <- Set.add t.keep rv;
        t.reg_bits <- Bitset.set t.reg_bits id);
    Vec.iter t.id2rv ~f:(fun rv ->
        if Rv.is_reg rv then
          t.reg_bits <- Bitset.set t.reg_bits t.$[rv]);
    alloc_arrays t

  (* initial: temporary registers, not preassigned a color and not yet
     processed by the algorithm. *)
  let init_initial t =
    init_initial_intern t;
    Func.blks t.fn |> Seq.iter ~f:(fun b ->
        Blk.insns b |> Seq.iter ~f:(fun i ->
            let insn = Insn.insn i in
            Set.iter (M.Insn.reads insn) ~f:(add_initial t);
            Set.iter (M.Insn.writes insn) ~f:(add_initial t)))
end
