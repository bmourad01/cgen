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
   - [initial]: temporary registers, not preassigned a color and not yet
     processed by the algorithm
*)

open Core
open Regular.Std
open Pseudo

module Lset = Label.Tree_set
module Id = Int
module H = Pairing_heap

type id = Id.t
type id_heap = id H.t
type id_elt = id H.Elt.t
type label_heap = Label.t H.t
type label_elt = Label.t H.Elt.t
type 'a label_tbl = 'a Label.Table.t
type 'a oarray = 'a Option_array.t

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

  type 'a rv_tbl = 'a Rv.Table.t

  (* Per-node data read by heap comparison functions (spill cost, move
     priority, freeze score).

     This exists to break the bootstrap cycle between `t` and the `cmp`
     closures for each heap.
  *)
  type data = {
    mutable degree     : int array;     (* Int.max_value = not yet seen *)
    mutable spill_cost : int array;     (* estimated spill cost of each node *)
    mutable reg_bits   : Bitset.t;      (* IDs that are pre-colored regs *)
    mutable slot_bits  : Bitset.t;      (* IDs that are stack-slot nodes *)
    mutable nuse       : int array;     (* use count for each node *)
    mutable live       : Live.t option; (* liveness analysis *)
    mutable defs       : Lset.t array;  (* definition instructions for each node *)
    mutable node_moves : Lset.t array;  (* move instructions for each node *)
    mutable amoves     : Lset.t;        (* active moves *)
  }

  let is_register' data id = Bitset.mem data.reg_bits id
  let is_slot' data id = Bitset.mem data.slot_bits id

  let create_data () = {
    degree = [||];
    spill_cost = [||];
    reg_bits = Bitset.empty;
    slot_bits = Bitset.empty;
    nuse = [||];
    live = None;
    defs = [||];
    node_moves = [||];
    amoves = Lset.empty;
  }

  type t = {
    mutable fn           : (M.Insn.t, M.Reg.t) func;
    rv2id                : id Rv.Table.t;  (* regvar to interned ID *)
    id2rv                : Rv.t Vec.t;     (* interned ID to regvar *)
    data                 : data;
    mutable wsimplify    : Bitset.t;       (* simplify worklist *)
    wfreeze              : id_heap;        (* freeze worklist *)
    mutable wfreeze_elts : id_elt oarray;
    mutable coalesced    : Bitset.t;       (* coalesced nodes *)
    mutable colored      : Bitset.t;       (* colored nodes *)
    mutable initial      : Bitset.t;       (* nodes not yet on a worklist *)
    mutable spilled      : Bitset.t;       (* spilled nodes *)
    mutable keep         : Rv.Set.t;       (* nodes that are live at the exits *)
    wmoves               : label_heap;     (* worklist moves *)
    wmoves_elts          : label_elt label_tbl;
    mutable cmoves       : Lset.t;         (* coalesced moves *)
    mutable kmoves       : Lset.t;         (* constrained moves *)
    mutable fmoves       : Lset.t;         (* frozen moves *)
    mutable adjlist      : Bitset.t array; (* adjacency list of the interference graph *)
    mutable colors       : int array;      (* node colors, -1 = not yet colored *)
    mutable alias        : id array;       (* node aliases (from combine/coalesce) *)
    mutable reload_bits  : Bitset.t;       (* IDs of reload temporaries from `rewrite_insn` *)
    wspill               : id_heap;
    mutable wspill_elts  : id_elt oarray;
    select               : id Stack.t;
    copies               : copy label_tbl;
    insn_blks            : (Label.t * id) label_tbl;
    slots                : Rv.t rv_tbl;
    phi_pairs            : Rv.Set.t rv_tbl;
    mutable types        : [Type.basic | `v128] Rv.Map.t;
    cfg                  : Pseudo.Cfg.t;
    loop                 : Loop.t;
    dom                  : Label.t Semi_nca.tree;
  }

  let intern t rv =
    Hashtbl.find_or_add t.rv2id rv ~default:(fun () ->
        let id = Vec.length t.id2rv in
        Vec.push t.id2rv rv;
        id)

  let (.$[]) t rv = Hashtbl.find_exn t.rv2id rv
  let (.![]) t id = Vec.get_exn t.id2rv id

  let num_nodes t = Vec.length t.id2rv

  (* Setup the state for a new round. *)
  let alloc_arrays t =
    let n = num_nodes t in
    t.data.degree <- Array.create ~len:n Int.max_value;
    t.data.spill_cost <- Array.create ~len:n 0;
    t.adjlist <- Array.create ~len:n Bitset.empty;
    t.data.nuse <- Array.create ~len:n 0;
    t.colors <- Array.create ~len:n (-1);
    t.alias <- Array.init n ~f:Fn.id;
    t.data.node_moves <- Array.create ~len:n Lset.empty;
    t.data.defs <- Array.create ~len:n Lset.empty;
    t.wspill_elts <- Option_array.create ~len:n;
    t.wfreeze_elts <- Option_array.create ~len:n

  let is_register t id = is_register' t.data id
  let is_slot t id = is_slot' t.data id
  let is_colored t id = Bitset.mem t.colored id

  (* Explicit registers and variables that correspond to stack slots should
     be excluded from consideration. *)
  let exclude_from_coloring t id = is_register t id || is_slot t id
  let can_be_colored t id = not (exclude_from_coloring t id)

  (* if n ∈ coalescedNodes then GetAlias(alias[n]) else n *)
  let rec alias t id =
    if Bitset.mem t.coalesced id
    then alias t t.alias.(id)
    else id

  let degree' t id =
    let d = t.data.degree.(id) in
    if d = Int.max_value then None else Some d

  let degree t id = t.data.degree.(id)

  let ensure_degree t id =
    if can_be_colored t id then
      let arr = t.data.degree in
      if arr.(id) = Int.max_value then arr.(id) <- 0

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

  let add_initial_id t id =
    if can_be_colored t id then
      t.initial <- Bitset.set t.initial id

  let add_initial t rv = add_initial_id t @@ intern t rv

  let reduce_type ~key a b = match a, b with
    | (#Type.imm as ia), (#Type.imm as ib)
      when Type.sizeof_imm ia < Type.sizeof_imm ib -> b
    | #Type.imm, #Type.imm -> a
    | (#Type.fp as fa), (#Type.fp as fb)
      when Type.sizeof_fp fa < Type.sizeof_fp fb -> b
    | #Type.fp, #Type.fp -> a
    | `v128, `v128 -> `v128
    | _ ->
      let sk = Format.asprintf "%a" Rv.pp key in
      let st t = match t with
        | #Type.basic as b ->
          Format.asprintf "%a" Type.pp_basic b
        | `v128 -> "v" in
      failwithf "type mismatch for var %s: %s is not compatible with %s"
        sk (st a) (st b) ()

  let update_types t insn =
    let types = M.Regalloc.writes_with_types insn in
    t.types <- Map.merge_skewed t.types types ~combine:reduce_type

  let is_phi_var t id =
    match Rv.which t.![id] with
    | First _ -> false
    | Second (v, _) ->
      match Dict.find (Func.dict t.fn) Tags.phi_var with
      | None -> false
      | Some p -> Set.mem p v

  let inc_use t id = t.data.nuse.(id) <- t.data.nuse.(id) + 1
  let num_uses t id = t.data.nuse.(id)

  let add_def t id label =
    t.data.defs.(id) <- Lset.add t.data.defs.(id) label

  let add_phi_pair t a b =
    let add rv partner =
      Hashtbl.update t.phi_pairs rv ~f:(fun s ->
          Set.add (Option.value s ~default:Rv.Set.empty) partner) in
    add a b; add b a

  let phi_pair_partners t rv =
    Hashtbl.find t.phi_pairs rv |> Option.value ~default:Rv.Set.empty

  module Wspill = struct
    (* Loop-weighted cost of a single use/def at `loop_depth`. *)
    let weight loop_depth = Int.pow 10 loop_depth

    (* Accumulate spill cost for node `id`. *)
    let update_cost ?(factor = 1) ~loop_depth t id =
      if can_be_colored t id then
        let w = weight loop_depth * factor in
        (* Use a saturating add to avoid signed overflow. *)
        let cur = t.data.spill_cost.(id) in
        t.data.spill_cost.(id) <-
          if w > Int.max_value - cur then Int.max_value else cur + w

    (* cost(v) = (Σ_{u ∈ uses(v)} weight(u)) / degree(v) *)
    let cost data id =
      let d = data.degree.(id) in
      if d = 0 || d = Int.max_value then Float.infinity else
        Int.to_float data.spill_cost.(id) /. Int.to_float d

    let cmp data a b = Float.compare (cost data a) (cost data b)
    let elt t id = Option_array.get t.wspill_elts id
    let has t id = Option_array.is_some t.wspill_elts id
    let set t id e = Option_array.set_some t.wspill_elts id e
    let clear t id = Option_array.set_none t.wspill_elts id
    let is_empty t = H.is_empty t.wspill

    let add t id =
      if can_be_colored t id && not (has t id) then
        let () = Logs.debug (fun m ->
            m "%s: adding %a to spill worklist%!"
              __FUNCTION__ Rv.pp t.![id]) in
        set t id (H.add_removable t.wspill id)

    let remove t id =
      elt t id |> Option.iter ~f:(fun e ->
          H.remove t.wspill e;
          clear t id)

    let update t id =
      elt t id |> Option.iter ~f:(fun e ->
          set t id (H.update t.wspill e id))

    let pop_exn t =
      let id = H.pop_exn t.wspill in
      clear t id;
      id
  end

  module Wmoves = struct
    let moves t id = t.data.node_moves.(id)
    let elt t m = Hashtbl.find t.wmoves_elts m
    let has t m = Hashtbl.mem t.wmoves_elts m
    let set t m e = Hashtbl.set t.wmoves_elts ~key:m ~data:e
    let clear t m = Hashtbl.remove t.wmoves_elts m
    let is_empty t = H.is_empty t.wmoves

    (* moveList[n] ∩ (activeMoves ∪ worklistMoves) *)
    let node_moves t id =
      Lset.fold (moves t id) ~init:Lset.empty ~f:(fun acc m ->
          if Lset.mem t.data.amoves m || has t m
          then Lset.add acc m
          else acc)

    let move_related t id = not (Lset.is_empty (node_moves t id))

    let add_move t label id =
      t.data.node_moves.(id) <- Lset.add t.data.node_moves.(id) label

    (* We can bypass the Briggs conservative heuristic if this move is
       trivially coalescable.

       Criteria:
       1. The source node is not precolored.
       2. This move is its only use.
       3. All definitions dominate the use.
       4. The source node is not live-out.
    *)
    let is_trivial_du_impl data ~insn_blks ~id2rv ~dom m v =
      not (is_register' data v) &&
      not (is_slot' data v) &&
      data.nuse.(v) = 1 &&
      match Hashtbl.find insn_blks m with
      | None -> false
      | Some (bm, om) ->
        let out = Live.outs (Option.value_exn data.live) bm in
        not (Set.mem out (Vec.get_exn id2rv v)) &&
        data.defs.(v) |> Lset.to_sequence |>
        Seq.for_all ~f:(fun d ->
            match Hashtbl.find insn_blks d with
            | None -> false
            | Some (bd, od) when Label.(bm = bd) ->
              Logs.debug (fun m ->
                  m "%s: bm=%a, om=%d, bd=%a, od=%d%!"
                    __FUNCTION__ Label.pp bm om Label.pp bd od);
              od < om
            | Some (bd, _) ->
              Semi_nca.Tree.is_descendant_of dom ~parent:bd bm)

    (* P(u,v) = S(u,v) * (W(u,v) / (1 + D'(u) + D'(v)))

       where:
       - S is the "safety factor"
       - W is the "weight" of the move
       - D' is the "effective degree"

       W follows our heuristic for spill priority: 10^loop_depth
    *)
    let priority_impl data ~copies ~id2rv ~insn_blks ~dom m =
      let c = Hashtbl.find_exn copies m in
      let exclude id = is_register' data id || is_slot' data id in
      let pu = exclude c.dst in
      let pv = exclude c.src in
      if pu && pv then 0.0 else
        (* Pre-colored nodes don't actually have a degree, so we need to
           scale the result such that a node with degree > K doesn't
           outweigh a node that is pre-colored. *)
        let effective_degree id p =
          let k = Regs.node_k (Vec.get_exn id2rv id) in
          let k' = k * 2 in
          if p then k' else
            let d = data.degree.(id) in
            if d <= k then d else
              (* If `d > K`, then we're OK with scaling off the tail end
                 towards our threshold of 2K, since such nodes are
                 effectively uncolorable until we allow `simplify` to make
                 progress. *)
              min (k' - 1) (k + ((d - k) / 2)) in
        let du = effective_degree c.dst pu in
        let dv = effective_degree c.src pv in
        let w = Float.of_int @@ Int.pow 10 c.loop in
        let p = w /. Float.of_int (1 + du + dv) in
        (* If this move is trivially coalescable, bump the weight so that
           it can coalesce earlier. *)
        let trivial = is_trivial_du_impl data ~insn_blks ~id2rv ~dom m c.src in
        let p = if trivial then p *. 2.0 else p in
        (* If one of the nodes is pre-colored, this coalesce will be much
           riskier. If both are pre-colored, avoid at all costs (see
           topmost condition). *)
        if pu || pv then p *. 0.25 else p

    let is_trivial_du t m v =
      is_trivial_du_impl t.data
        ~insn_blks:t.insn_blks
        ~id2rv:t.id2rv
        ~dom:t.dom
        m v

    let priority t m =
      priority_impl t.data
        ~copies:t.copies
        ~id2rv:t.id2rv
        ~insn_blks:t.insn_blks
        ~dom:t.dom
        m

    let cmp data ~copies ~id2rv ~insn_blks ~dom a b =
      Float.compare
        (priority_impl data ~copies ~id2rv ~insn_blks ~dom b)
        (priority_impl data ~copies ~id2rv ~insn_blks ~dom a)

    let add t m =
      if not (has t m) then
        set t m (H.add_removable t.wmoves m)

    let remove t m =
      elt t m |> Option.iter ~f:(fun e ->
          H.remove t.wmoves e;
          clear t m)

    let update t m =
      elt t m |> Option.iter ~f:(fun e ->
          set t m (H.update t.wmoves e m))

    let update_for t id =
      t.data.node_moves.(id) |> Lset.iter ~f:(update t)

    let pop_exn t =
      let m = H.pop_exn t.wmoves in
      clear t m;
      m

    let reset t =
      Hashtbl.clear t.wmoves_elts;
      H.clear t.wmoves
  end

  module Wfreeze = struct
    let elt t id = Option_array.get t.wfreeze_elts id
    let has t id = Option_array.is_some t.wfreeze_elts id
    let set t id e = Option_array.set_some t.wfreeze_elts id e
    let clear t id = Option_array.set_none t.wfreeze_elts id
    let is_empty t = H.is_empty t.wfreeze

    let phi_weight_coeff = 5

    let cost data ~wmoves_elts ~copies ~id2rv ~phi_var id =
      let mvs = Lset.fold data.node_moves.(id) ~init:Lset.empty ~f:(fun acc m ->
          if Lset.mem data.amoves m || Hashtbl.mem wmoves_elts m
          then Lset.add acc m else acc) in
      (* Freeze the node whose freezing loses the least loop-weighted value.
         Each active move contributes its loop depth to the cost of freezing
         this node. Phi-related moves (back-edge copies where the destination
         is a phi var) are weighted by an additional coefficient to defer
         freezing of phi vars. Coalescing those moves eliminates loop-carried
         register shuffles, so losing them is much more expensive than losing
         an ordinary copy. *)
      let non_phi_weight, phi_weight =
        Lset.to_sequence mvs |>
        Seq.filter_map ~f:(Hashtbl.find copies) |>
        Seq.fold ~init:(0, 0) ~f:(fun (np, pw) (copy : copy) ->
            let w = copy.loop in
            match Rv.which (Vec.get_exn id2rv copy.dst) with
            | Second (v, _) when Set.mem phi_var v -> np, pw + w
            | _ -> np + w, pw) in
      non_phi_weight + phi_weight_coeff * phi_weight

    let cmp data ~wmoves_elts ~copies ~id2rv ~phi_var a b =
      let ca = cost data ~wmoves_elts ~copies ~id2rv ~phi_var a in
      let cb = cost data ~wmoves_elts ~copies ~id2rv ~phi_var b in
      let c = Int.compare ca cb in
      (* Break ties by node ID. *)
      if c <> 0 then c else Int.compare a b

    let add t id =
      if can_be_colored t id && not (has t id) then
        set t id (H.add_removable t.wfreeze id)

    let remove t id =
      elt t id |> Option.iter ~f:(fun e ->
          H.remove t.wfreeze e;
          clear t id)

    let update t id =
      elt t id |> Option.iter ~f:(fun e ->
          set t id (H.update t.wfreeze e id))

    let update_for_move t m =
      match Hashtbl.find t.copies m with
      | None -> ()
      | Some c ->
        update t (alias t c.dst);
        update t (alias t c.src)

    let pop_exn t =
      let id = H.pop_exn t.wfreeze in
      clear t id;
      id

    let reset t =
      Option_array.clear t.wfreeze_elts;
      H.clear t.wfreeze
  end

  let inc_degree t id =
    t.data.degree.(id) <- t.data.degree.(id) + 1;
    Wspill.update t id

  let dec_degree t id =
    t.data.degree.(id) <- max 0 (t.data.degree.(id) - 1);
    Wspill.update t id;
    Wmoves.update_for t id

  let create fn =
    let cfg = Pseudo.Cfg.create fn
        ~is_barrier:M.Insn.is_barrier
        ~is_pseudo:M.Insn.is_pseudo
        ~dests:M.Insn.dests in
    let dom = Semi_nca.compute (module Pseudo.Cfg) cfg Label.pseudoentry in
    let loop = Loop.analyze ~dom ~name:(Pseudo.Func.name fn) cfg in
    let copies = Label.Table.create () in
    let insn_blks = Label.Table.create () in
    let id2rv = Vec.create () in
    let wmoves_elts = Label.Table.create () in
    let phi_var =
      Dict.find (Func.dict fn) Tags.phi_var |>
      Option.value ~default:Var.Set.empty in
    let data = create_data () in
    let wspill_cmp = Wspill.cmp data in
    let wmoves_cmp = Wmoves.cmp data ~copies ~id2rv ~insn_blks ~dom in
    let wfreeze_cmp = Wfreeze.cmp data ~wmoves_elts ~copies ~id2rv ~phi_var in {
      fn;
      rv2id = Rv.Table.create ();
      id2rv;
      data;
      wsimplify = Bitset.empty;
      wfreeze = H.create ~cmp:wfreeze_cmp ();
      wfreeze_elts = Option_array.empty;
      coalesced = Bitset.empty;
      colored = Bitset.empty;
      initial = Bitset.empty;
      spilled = Bitset.empty;
      keep = Rv.Set.empty;
      wmoves = H.create ~cmp:wmoves_cmp ();
      wmoves_elts;
      cmoves = Lset.empty;
      kmoves = Lset.empty;
      fmoves = Lset.empty;
      adjlist = [||];
      colors = [||];
      alias = [||];
      reload_bits = Bitset.empty;
      wspill = H.create ~cmp:wspill_cmp ();
      wspill_elts = Option_array.empty;
      select = Stack.create ();
      copies;
      insn_blks;
      slots = Rv.Table.create ();
      phi_pairs = Rv.Table.create ();
      types = Rv.Map.empty;
      cfg;
      loop;
      dom;
    }

  let initialize t =
    (* Intern all variables mentioned in the function
       and add them to `initial`. *)
    let blks = Func.map_of_blks t.fn in
    Semi_nca.Tree.preorder t.dom |>
    Seq.filter_map ~f:(Label.Tree.find blks) |>
    Seq.iter ~f:(fun b ->
        Blk.insns b |> Seq.iter ~f:(fun i ->
            let insn = Insn.insn i in
            M.Insn.reads insn |> Set.iter ~f:(add_initial t);
            M.Insn.writes insn |> Set.iter ~f:(add_initial t);
            update_types t insn));
    (* Intern `sp` and the return registers. These are also
       "initially live", which seeds the liveness analysis. *)
    let sp = Rv.reg M.Reg.sp in
    t.keep <- Set.add t.keep sp;
    t.data.reg_bits <- Bitset.set t.data.reg_bits (intern t sp);
    Func.rets t.fn |> Seq.iter ~f:(fun r ->
        let rv = Rv.reg r in
        let id = intern t rv in
        t.keep <- Set.add t.keep rv;
        t.data.reg_bits <- Bitset.set t.data.reg_bits id);
    (* Record which nodes are precolored (hardcoded registers). *)
    Vec.iter t.id2rv ~f:(fun rv ->
        if Rv.is_reg rv then
          t.data.reg_bits <- Bitset.set t.data.reg_bits t.$[rv]);
    (* Setup the remaining state for the first round. *)
    alloc_arrays t

  (* Verify the stated invariants in the IRC paper:

     - Partition invariant: every colorable node is in exactly one set.
     - Degree invariant: degree[u] counts active neighbours exactly.
     - `wfreeze`: degree < K AND move-related.
     - `wspill`:  degree >= K.
     - `wsimplify`: degree < K AND NOT move-related.
  *)
  let check_invariants t =
    let n = num_nodes t in
    let wfreeze_set = H.fold t.wfreeze ~init:Bitset.empty ~f:Bitset.set in
    let wspill_set = H.fold t.wspill ~init:Bitset.empty ~f:Bitset.set in
    let active =
      Bitset.union t.wsimplify
        (Bitset.union wfreeze_set
           (Bitset.union wspill_set t.data.reg_bits)) in
    (* Degree invariant *)
    let check_degree id =
      let expected =
        Bitset.fold t.adjlist.(id) ~init:0
          ~f:(fun acc k -> if Bitset.mem active k then acc + 1 else acc) in
      let actual = t.data.degree.(id) in
      if actual <> expected then
        failwithf "degree invariant violated for id %d: degree=%d expected=%d"
          id actual expected () in
    Bitset.iter t.wsimplify ~f:check_degree;
    H.iter t.wfreeze ~f:check_degree;
    H.iter t.wspill ~f:check_degree;
    (* wsimplify invariant: degree < K and not move-related *)
    Bitset.iter t.wsimplify ~f:(fun id ->
        let d = t.data.degree.(id) in
        let k = Regs.node_k t.![id] in
        if d >= k then
          failwithf "wsimplify invariant: id %d degree=%d >= K=%d" id d k ();
        if Wmoves.move_related t id then
          failwithf "wsimplify invariant: id %d is move-related" id ());
    (* wfreeze invariant: degree < K and move-related *)
    H.iter t.wfreeze ~f:(fun id ->
        let d = t.data.degree.(id) in
        let k = Regs.node_k t.![id] in
        if d >= k then
          failwithf "wfreeze invariant: id %d degree=%d >= K=%d" id d k ();
        if not (Wmoves.move_related t id) then
          failwithf "wfreeze invariant: id %d not move-related" id ());
    (* wspill invariant: degree >= K *)
    H.iter t.wspill ~f:(fun id ->
        let d = t.data.degree.(id) in
        let k = Regs.node_k t.![id] in
        if d < k then
          failwithf "wspill invariant: id %d degree=%d < K=%d" id d k ());
    (* Partition invariant: each colorable node in exactly one set *)
    let select_set = Stack.fold t.select ~init:Bitset.empty ~f:Bitset.set in
    let partitions = [
      ("wsimplify", t.wsimplify);
      ("wfreeze",   wfreeze_set);
      ("wspill",    wspill_set);
      ("coalesced", t.coalesced);
      ("colored",   t.colored);
      ("select",    select_set);
      ("initial",   t.initial);
    ] in
    let partition_members id =
      List.filter_map partitions ~f:(fun (name, s) ->
          Option.some_if (Bitset.mem s id) name) in
    for id = 0 to n - 1 do
      if can_be_colored t id then
        match partition_members id with
        | [] | [_] -> ()
        | names ->
          failwithf "partition invariant: id %d in %s"
            id (String.concat ~sep:", " names) ()
    done;
    (* Adjacency symmetry *)
    for u = 0 to n - 1 do
      Bitset.iter t.adjlist.(u) ~f:(fun v ->
          if not (Bitset.mem t.adjlist.(v) u) then
            failwithf "adjacency symmetry: (%d,%d) present but (%d,%d) absent"
              u v v u ())
    done
end
