(* Implementation of "Iterated Register Coalescing (1996)"
   by L. George and A. Appel *)

open Core
open Regular.Std
open Pseudo

module Lset = Label.Tree_set
module LT = Label.Dense_table

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax
  open Regalloc_irc_state.Make(M)

  module RA = M.Regalloc

  (* Adds an edge between `u` and `v` in the interference graph. *)
  let add_edge t u v =
    (* A node cannot interfere with itself, nor a node with a different
       register class. Nodes that correspond to slots are excluded. *)
    ensure_degree t u;
    ensure_degree t v;
    if u <> v
    && not (has_edge t u v)
    && Regs.same_class_node t.![u] t.![v]
    && not (is_slot t u)
    && not (is_slot t v) then begin
      add_adjlist t u v;
      add_adjlist t v u;
      if can_be_colored t u then inc_degree t u;
      if can_be_colored t v then inc_degree t v
    end

  let build_insn ~loop_depth t out i =
    let label = Insn.label i in
    let insn = Insn.insn i in
    let use = M.Insn.reads insn in
    let def = M.Insn.writes insn in
    Set.iter use ~f:(fun rv ->
        let u = t.$[rv] in
        Wspill.update_cost ~loop_depth t u;
        inc_use t u);
    Set.iter def ~f:(fun rv ->
        let d = t.$[rv] in
        if is_phi_var t d then
          Wspill.update_cost ~factor:2 ~loop_depth t d);
    (* if isMoveInstruction(I) then *)
    let+ out = match RA.is_copy insn with
      | None -> !!out
      | Some (drv, srv) ->
        let d = t.$[drv] and s = t.$[srv] in
        (* This is an invariant that is required of `RA.is_copy`; better
           to fail loudly here than silently introduce errors. *)
        let+ () = C.unless (Regs.same_class_node drv srv) @@ fun () ->
          C.failf "In Regalloc.build_insn: got a copy instruction `%a` between \
                   between two different register classes (%a, %a)"
            (Insn.pp M.Insn.pp) i Rv.pp drv Rv.pp srv () in
        (* live := live ∖ use(I) *)
        let out = Set.diff out use in
        (* ∀ n ∈ def(I) ∪ use(I)
             moveList[n] := moveList[n] ∪ {I} *)
        Wmoves.add_move t label d;
        Wmoves.add_move t label s;
        LT.set t.copies ~key:label ~data:{
          dst = d;
          src = s;
          loop = loop_depth;
        };
        (* Persist phi-copy relationships for cross-round slot coalescing.
           `t.copies` is cleared each round, but `phi_pairs` survives. *)
        if is_phi_var t d || is_phi_var t s then
          add_phi_pair t drv srv;
        (* worklistMoves := worklistMoves ∪ {I} *)
        Wmoves.add t label;
        out in
    (* live := live ∪ def(I) *)
    let out = Set.union out def in
    (* ∀ d ∈ def(I) *)
    Set.iter def ~f:(fun rv ->
        (* ∀ l ∈ live
             AddEdge(l,d) *)
        let d = t.$[rv] in
        add_def t d label;
        Set.iter out ~f:(fun rv -> add_edge t t.$[rv] d));
    (* live := use(I) ∪ (live ∖ def(I)) *)
    Set.union use (Set.diff out def)

  (* Build the interference graph and other initial state for the
     algorithm. *)
  let build t =
    (* ∀ b ∈ blocks in program *)
    let live = Option.value_exn t.data.live in
    Func.blks t.fn |> C.Seq.iter ~f:(fun b ->
        let l = Blk.label b in
        let loop_depth = match Loop.blk t.loop l with
          | None -> 0
          | Some lp ->
            (* NB: levels start at 0 *)
            (Loop.(level (get t.loop lp)) :> int) + 1 in
        (* live := liveOut(b) *)
        let out = ref @@ Live.outs live l in
        (* ∀ I ∈ instructions(b) in reverse order *)
        let ord = ref (Blk.num_insns b - 1) in
        Blk.insns b ~rev:true |> C.Seq.iter ~f:(fun i ->
            LT.set t.insn_blks ~key:(Insn.label i) ~data:(l, !ord);
            let+ out' = build_insn ~loop_depth t !out i in
            out := out';
            decr ord))

  (* Initialize the worklists. *)
  let make_worklist t =
    Bitset.iter t.initial ~f:(fun id ->
        (* If we introduced `id` during spilling, but later removed
           its definition during dead code elimination, then it
           won't have a degree. *)
        degree' t id |> Option.iter ~f:(fun d ->
            if d >= Regs.node_k t.![id] then
              Wspill.add t id
            else if Wmoves.move_related t id then
              Wfreeze.add t id
            else
              t.wsimplify <- Bitset.set t.wsimplify id));
    t.initial <- Bitset.empty

  let enable_moves_one t n =
    (* ∀ m ∈ NodeMoves(n) *)
    Wmoves.node_moves t n |> Lset.iter ~f:(fun m ->
        (* if m ∈ activeMoves then *)
        if Lset.mem t.data.amoves m then begin
          Logs.debug (fun m_ ->
              m_ "%s: enabling move %a for node %a%!"
                __FUNCTION__ Label.pp m Rv.pp t.![n]);
          (* activeMoves := activeMoves ∖ {m} *)
          t.data.amoves <- Lset.remove t.data.amoves m;
          (* worklistMoves := worklistMoves ∪ {m} *)
          Wmoves.add t m;
          Wfreeze.update_for_move t m;
        end)

  let enable_moves t nodes =
    (* ∀ n ∈ nodes *)
    Bitset.iter nodes ~f:(enable_moves_one t)

  (* Simulate removing a node from the interference graph (this is what
     the `degree` table is for). *)
  let decrement_degree t id =
    match degree' t id with
    | None ->
      assert (exclude_from_coloring t id)
    | Some d ->
      assert (can_be_colored t id);
      (* let d = degree[m]
         degree[m] := d-1 *)
      dec_degree t id;
      (* if d = K then *)
      if d = Regs.node_k t.![id] then begin
        (* EnableMoves({m} ∪ Adjacent(m)) *)
        enable_moves t (Bitset.set (adjacent t id) id);
        (* spillWorklist := spillWorklist ∖ {m} *)
        Wspill.remove t id;
        (* if MoveRelated(m) then
             freezeWorklist := freezeWorklist ∪ {m}
           else
             simplifyWorklist := simplifyWorklist ∪ {m} *)
        if Wmoves.move_related t id
        then Wfreeze.add t id
        else t.wsimplify <- Bitset.set t.wsimplify id
      end

  (* pre: wsimplify is not empty *)
  let simplify t =
    (* let n ∈ simplifyWorklist
       simplifyWorklist := simplifyWorklist ∖ {n} *)
    let id, wsimplify' = Bitset.pop_min_elt_exn t.wsimplify in
    t.wsimplify <- wsimplify';
    (* push(n, selectStack) *)
    if can_be_colored t id then begin
      Logs.debug (fun m -> m "%s: selecting %a%!" __FUNCTION__ Rv.pp t.![id]);
      Stack.push t.select id
    end;
    (* ∀ m ∈ Adjacent(n) *)
    Bitset.iter (adjacent t id) ~f:(decrement_degree t)

  let should_add_to_worklist t id =
    (* u ∉ precolored *)
    can_be_colored t id &&
    (* not(MoveRelated(u)) *)
    not (Wmoves.move_related t id) &&
    (* degree[u] < K *)
    degree t id < Regs.node_k t.![id]

  let add_worklist t id = if should_add_to_worklist t id then begin
      (* freezeWorklist := freezeWorklist ∖ {u} *)
      Wfreeze.remove t id;
      (* simplifyWorklist := simplifyWorklist ∪ {u} *)
      t.wsimplify <- Bitset.set t.wsimplify id;
    end

  let george_ok t a r =
    let res =
      (* t ∈ precolored *)
      exclude_from_coloring t a ||
      (* degree[t] < K *)
      degree t a < Regs.node_k t.![a] ||
      (* (a,r) ∈ adjSet *)
      has_edge t a r in
    Logs.debug (fun m ->
        m "%s: %a, %a: %b%!"
          __FUNCTION__ Rv.pp t.![a] Rv.pp t.![r] res);
    res

  (* George's conservative coalescing criterion: all high-degree neighbors
     of `v` are neighbors of `u`. *)
  let all_adjacent_ok t u v =
    (* ∀ t ∈ Adjacent(v), OK(t,u)  *)
    Bitset.for_all (adjacent t v) ~f:(fun a -> george_ok t a u)

  (* Briggs conservative coalescing heuristic.

     let k = 0
     ∀ n ∈ nodes
       if degree[n] >= k then k := k + 1
     return (k < K)
  *)
  let conservative t nodes =
    Bitset.fold nodes ~init:0 ~f:(fun k id ->
        if degree t id >= Regs.node_k t.![id] then k + 1 else k)

  (* Conservative(Adjacent(u) ∪ Adjacent(v)) *)
  let conservative_adj t u v =
    assert (Regs.same_class_node t.![u] t.![v]);
    let nodes = Bitset.union (adjacent t u) (adjacent t v) in
    let nk = Regs.node_k t.![u] in
    let k = conservative t nodes in
    Logs.debug (fun m ->
        m "%s: u=%a, v=%a, k=%d, nk=%d%!"
          __FUNCTION__ Rv.pp t.![u] Rv.pp t.![v] k nk);
    k < nk

  (* XXX: the algorithm in the paper does:

     AddEdge(t, u)
     DecrementDegree(t)

     but this seems to be rather bug-prone. If `t` and
     `u` already interfere, then we should just decrement
     the degree of `t` to simulate removing `v`.

     Otherwise, we add the edge and increment the degree
     of `u`, leaving the degree of `t` unchanged.
  *)
  let combine_edge t u v =
    let e = has_edge t u v in
    Logs.debug (fun m ->
        m "%s: combining edge u=%a, v=%a, has_edge=%b%!"
          __FUNCTION__ Rv.pp t.![u] Rv.pp t.![v] e);
    if e then
      decrement_degree t v
    else begin
      add_adjlist t u v;
      add_adjlist t v u;
      if can_be_colored t u then inc_degree t u;
    end

  (* Combine `v` with `u` in the interference graph, where
     `u` is the destination. *)
  let combine t u v =
    Logs.debug (fun m ->
        m "%s: combining u=%a with v=%a%!"
          __FUNCTION__ Rv.pp t.![u] Rv.pp t.![v]);
    (* if v ∈ freezeWorklist *)
    if Wfreeze.has t v then
      (* freezeWorklist := freezeWorklist ∖ {v} *)
      Wfreeze.remove t v
    else
      (* spillWorklist := spillWorklist ∖ {v} *)
      Wspill.remove t v;
    (* coalescedNodes := coalescedNodes ∪ {v} *)
    t.coalesced <- Bitset.set t.coalesced v;
    (* alias[v] := u *)
    t.alias.(v) <- u;
    (* nodeMoves[u] := nodeMoves[u] ∪ nodeMoves[v] *)
    t.data.node_moves.(u) <- Lset.union t.data.node_moves.(u) t.data.node_moves.(v);
    Wfreeze.update t u;
    (* ∀ t ∈ Adjacent(v) *)
    Bitset.iter (adjacent t v) ~f:(combine_edge t u);
    (* Appel book erratum: since our `combine_edge` does not call
       DecrementDegree on new-edge neighbors (to avoid spurious
       EnableMoves), v's active moves would otherwise remain in
       activeMoves indefinitely, keeping their partner nodes
       falsely move-related. *)
    enable_moves_one t v;
    if (* degree[u] >= K *)
      degree t u >= Regs.node_k t.![u] &&
      (* u ∈ freezeWorklist *)
      Wfreeze.has t u
    then
      (* freezeWorklist := freezeWorklist ∖ {u} *)
      let () = Wfreeze.remove t u in
      (* spillWorklist := spillWorklist ∪ {u} *)
      Wspill.add t u

  (* pre: wmoves is not empty *)
  let coalesce t =
    (* let m_(=copy(x,y)) ∈ worklistMoves *)
    let m = Wmoves.pop_exn t in
    let c = LT.find_exn t.copies m in
    (* x := GetAlias(x) *)
    let x = alias t c.dst in
    (* y := GetAlias(y) *)
    let y = alias t c.src in
    (* if y ∈ precolored then
         let (u,v) = (y,x)
       else
         let (u,v) = (x,y) *)
    let u, v = if exclude_from_coloring t y then y, x else x, y in
    Logs.debug (fun m_ ->
        m_ "%s: looking at move %a, score=%g, u=%a, v=%a%!"
          __FUNCTION__ Label.pp m (Wmoves.priority t m) Rv.pp t.![u] Rv.pp t.![v]);
    (* if u = v then *)
    if u = v then
      (* coalescedMoves := coalescedMoves ∪ {m} *)
      let () = t.cmoves <- Lset.add t.cmoves m in
      Logs.debug (fun m -> m "%s: already coalesced%!" __FUNCTION__);
      (* AddWorkList(u) *)
      add_worklist t u;
      (* m is no longer active; update freeze priority for u *)
      Wfreeze.update t u
    else if
      (* v ∈ precolored *)
      exclude_from_coloring t v ||
      (* (u,v) ∈ adjSet *)
      has_edge t u v
    then
      (* constrainedMoves := constrainedMoves ∪ {m} *)
      let () = t.kmoves <- Lset.add t.kmoves m in
      Logs.debug (fun m_ ->
          m_ "%s: constraining %a%!" __FUNCTION__ Label.pp m);
      (* addWorkList(u) *)
      add_worklist t u;
      (* addWorkList(v) *)
      add_worklist t v;
      (* m is no longer active; update freeze priorities for u and v *)
      Wfreeze.update t u;
      Wfreeze.update t v
    else if
      (* u ∈ precolored ∧ (∀ t ∈ Adjacent(v), OK(t,u)) *)
      (exclude_from_coloring t u && all_adjacent_ok t u v) ||
      (* u ∉ precolored ∧ Conservative(Adjacent(u), Adjacent(v)) *)
      (can_be_colored t u && (Wmoves.is_trivial_du t m v || conservative_adj t u v))
    then
      (* coalescedMoves := coalescedMoves ∪ {m} *)
      let () = t.cmoves <- Lset.add t.cmoves m in
      (* Combine(u,v) *)
      combine t u v;
      (* AddWorkList(u) *)
      add_worklist t u
    else
      (* activeMoves := activeMoves ∪ {m} *)
      let () = t.data.amoves <- Lset.add t.data.amoves m in
      Logs.debug (fun m -> m "%s: adding to active moves%!" __FUNCTION__)

  let freeze_moves t u =
    let u' = alias t u in
    (* ∀ m ∈ NodeMoves(u) *)
    Wmoves.node_moves t u |> Lset.iter ~f:(fun m ->
        let c = LT.find_exn t.copies m in
        (* GetAlias(src); if it equals GetAlias(u), v is the dst side. *)
        let y = alias t c.src in
        let v = if y = u' then alias t c.dst else y in
        (* if m ∈ activeMoves *)
        if Lset.mem t.data.amoves m then
          (* activeMoves := activeMoves ∖ {m} *)
          t.data.amoves <- Lset.remove t.data.amoves m
        else
          (* worklistMoves := worklistMoves ∖ {m} *)
          Wmoves.remove t m;
        (* frozenMoves := frozenMoves ∪ {m} *)
        Logs.debug (fun m_ ->
            m_ "%s: freezing move %a, v=%a"
              __FUNCTION__ Label.pp m Rv.pp t.![v]);
        t.fmoves <- Lset.add t.fmoves m;
        (* if NodeMoves(v) = {} ∧ degree[v] < K ∧ v not precolored *)
        if Lset.is_empty (Wmoves.node_moves t v)
        && degree t v < Regs.node_k t.![v]
        && not (exclude_from_coloring t v) then begin
          (* freezeWorklist := freezeWorklist ∖ {v} *)
          Wfreeze.remove t v;
          (* simplifyWorklist := simplifyWorklist ∪ {v} *)
          t.wsimplify <- Bitset.set t.wsimplify v;
        end else
          Wfreeze.update t v)

  (* pre: wfreeze is not empty *)
  let freeze t =
    (* let u ∈ freezeWorklist
       freezeWorklist := freezeWorklist ∖ {u} *)
    let u = Wfreeze.pop_exn t in
    Logs.debug (fun m -> m "%s: frozen node u=%a%!" __FUNCTION__ Rv.pp t.![u]);
    (* simplifyWorklist := simplifyWorklist ∪ {u} *)
    t.wsimplify <- Bitset.set t.wsimplify u;
    (* FreezeMoves(u) *)
    freeze_moves t u

  let select_spill t =
    let m = Wspill.pop_exn t in
    Logs.debug (fun m_ ->
        m_ "%s: selecting spill node %a%!"
          __FUNCTION__ Rv.pp t.![m]);
    (* spillWorklist := spillWorklist ∖ {m} *)
    Wspill.clear t m;
    (* FreezeMoves(m) *)
    freeze_moves t m;
    (* Instead of going through `wsimplify`, we'll inline the relevant
       logic here. This is to avoid violating the invariants of the
       simplify worklist. *)
    if can_be_colored t m then Stack.push t.select m;
    Bitset.iter (adjacent t m) ~f:(decrement_degree t)

  (* For all neighbors of `id` that have a color, remove them from the
     set of his available colors. *)
  let free_colors t id k =
    (* ∀ w ∈ adjList[n] *)
    adjlist t id |> Bitset.enum |> Seq.map ~f:(alias t) |>
    (* if GetAlias(w) ∈ (coloredNodes ∪ precolored) then *)
    Seq.filter ~f:(fun w -> is_register t w || is_colored t w) |>
    (* okColors := okColors ∖ {color[GetAlias(w)]} *)
    Seq.filter_map ~f:(color t) |>
    Seq.fold ~init:(Bitset.init k) ~f:Bitset.clear

  (* If a copy-related neighbor is already colored with a color in `cs`,
     return that color. This is known as move biasing: by reusing the
     neighbor's color we eliminate the copy instruction. *)
  let preferred_color t id cs =
    Wmoves.moves t id |> Lset.to_sequence |>
    Seq.filter_map ~f:(LT.find t.copies) |>
    Seq.filter_map ~f:(fun c ->
        let other = if c.dst = id then c.src else c.dst in
        color t (alias t other)) |>
    Seq.find ~f:(Bitset.mem cs)

  let assign_colors t =
    (* while SelectStack is not empty
       let n = pop(SelectStack) *)
    Stack.until_empty t.select (fun id ->
        assert (can_be_colored t id);
        (* okColors := {0,...,K-1} *)
        let k = Regs.node_k t.![id] in
        let cs = free_colors t id k in
        (* if okColors = {} then *)
        match Bitset.min_elt cs with
        | None ->
          (* spilledNodes := spilledNodes ∪ {n} *)
          t.spilled <- Bitset.set t.spilled id
        | Some default ->
          (* coloredNodes := coloredNodes ∪ {n} *)
          t.colored <- Bitset.set t.colored id;
          (* Prefer a color that eliminates a copy (move biasing),
             falling back to the minimum available color. *)
          let c = Option.value (preferred_color t id cs) ~default in
          set_color t id c);
    (* ∀ n ∈ coalescedNodes *)
    Bitset.iter t.coalesced ~f:(fun id ->
        (* color[n] := color[GetAlias(n)] *)
        alias t id |> color t |> Option.iter ~f:(set_color t id))

  let typeof t v = match Map.find t.types v with
    | None -> C.failf "no type available for spilled node %a" Rv.pp v ()
    | Some ty -> !!ty

  (* Find an existing slot of comparable size that doesn't interfere
     with `id`. *)
  let find_reusable_slot t m id size =
    Map.find m size |> Option.bind ~f:(fun rvs ->
        List.find rvs ~f:(fun rv -> not (has_edge t id t.$[rv])))

  (* Remove `r'` from m so it can't be assigned to a third variable.
     The slot now has two occupants (the original owner and `r`).
     `find_reusable_slot` only checks interference with the original
     owner, so a third variable that doesn't interfere with the
     original owner could incorrectly reuse the slot, but the
     second occupant (`r`) may be live at the exit and need the slot.
     Removing `r'` prevents this triple aliasing. *)
  let update_slot_map m size r' =
    Map.change m size ~f:(function
        | None -> None
        | Some rvs ->
          let rvs' = List.filter rvs ~f:(Rv.((<>)) r') in
          if List.is_empty rvs' then None else Some rvs')

  (* Find the slot already assigned to a copy-related spilled node, if any,
     preferring it to eliminate the slot-to-slot copy in the admin block.
     This is the stack-slot analogue of move biasing in assign_colors. *)
  let preferred_slot t id =
    let rv = t.![id] in
    let try_slot partner =
      (* Only use a partner's slot when the partner is being spilled
         in this same round. `alloc_arrays` clears `t.adjlist` between
         rounds, so `has_edge` returns `false` for genuine interferences
         that now correspond to old slots, and coalescing to an old slot
         aliases live ranges. *)
      if not (Bitset.mem t.spilled t.$[partner]) then None else
        Hashtbl.find t.slots partner |> Option.bind ~f:(fun slot ->
            Option.some_if (not (has_edge t id t.$[slot])) slot) in
    phi_pair_partners t rv |> Set.to_sequence |>
    Seq.filter_map ~f:try_slot |> Seq.hd |> function
    | Some _ as phi -> phi
    | None ->
      (* Same-round fallback: check current-round copies. *)
      Wmoves.moves t id |> Lset.to_sequence |>
      Seq.filter_map ~f:(LT.find t.copies) |>
      Seq.filter_map ~f:(fun c ->
          let other = if c.dst = id then c.src else c.dst in
          try_slot t.![other]) |> Seq.hd

  (* Create slots for spilled nodes. *)
  let make_slots t =
    let+ slots, _ =
      Bitset.enum t.spilled |>
      C.Seq.fold ~init:([], Int.Map.empty) ~f:(fun (acc, m) id ->
          match Rv.which t.![id] with
          | First _ -> assert false
          | Second (v, _) ->
            let+ size = typeof t t.![id] >>| function
              | #Type.basic as b -> Type.sizeof_basic b / 8
              | `v128 -> 16 in
            let r = Rv.var GPR v in
            let rid = t.$[r] in
            let reuse r' =
              Logs.debug (fun m ->
                  m "%s: re-using slot %a for spilled node %a%!"
                    __FUNCTION__ Rv.pp r' Rv.pp r);
              Hashtbl.set t.slots ~key:r ~data:r';
              t.data.slot_bits <- Bitset.set t.data.slot_bits rid;
              acc, update_slot_map m size r' in
            match preferred_slot t id with
            | Some r' -> reuse r'
            | None ->
              match find_reusable_slot t m id size with
              | Some r' -> reuse r'
              | None ->
                Logs.debug (fun m ->
                    m "%s: spilling %a to new slot%!"
                      __FUNCTION__ Rv.pp r);
                let s = Virtual.Slot.create_exn v ~size ~align:size in
                Hashtbl.set t.slots ~key:r ~data:r;
                t.data.slot_bits <- Bitset.set t.data.slot_bits rid;
                s :: acc, Map.add_multi m ~key:size ~data:r) in
    t.fn <- Func.insert_slots t.fn slots

  (* If both sides of a copy are spilled to the same slot, the copy is a
     no-op: the source slot already holds the correct value for the dest.
     Skip the instruction entirely rather than generating load+copy+store. *)
  let same_slot_copy t insn = match RA.is_copy insn with
    | Some (drv, srv) ->
      Bitset.mem t.spilled t.$[drv] &&
      Bitset.mem t.spilled t.$[srv] &&
      Option.equal Rv.equal
        (Hashtbl.find t.slots drv)
        (Hashtbl.find t.slots srv)
    | _ -> false

  (* Rewrite a single instruction to spill and reload variables. *)
  let rewrite_insn t reload ivec i =
    let insn = Insn.insn i in
    let use = M.Insn.reads insn in
    let def = M.Insn.writes insn in
    let+ fetch, store, subst, reload =
      let init = [], [], Rv.Map.empty, reload in
      Set.union use def |> Set.to_sequence |>
      Seq.filter ~f:(fun rv -> Bitset.mem t.spilled t.$[rv]) |>
      C.Seq.fold ~init ~f:(fun (f, s, m, rl) v ->
          let* ty = typeof t v in
          let slot = Hashtbl.find_exn t.slots v in
          let is_use = Set.mem use v and is_def = Set.mem def v in
          (* Optimization: if `v` is a pure use and we already loaded it
             earlier in this block (it's in the reload cache `rl`), reuse
             the existing temp without emitting another load. *)
          match Map.find rl v with
          | Some v' when is_use && not is_def ->
            let m' = Map.set m ~key:v ~data:v' in
            !!(f, s, m', rl)
          | _ ->
            (* Create a new temporary v_i for each definition and each use
               not already satisfied by the reload cache. *)
            let* v' = C.Var.fresh >>| Rv.var (Regs.classof v) in
            (* a fetch before each use of a v_i; cache it for later uses *)
            let* f', rl = if is_use then
                let+ label = C.Label.fresh in
                let insn = RA.load_from_slot ty ~dst:v' ~src:slot in
                Insn.create ~label ~insn :: f,
                Map.set rl ~key:v ~data:v'
              else !!(f, rl) in
            (* Insert a store after each definition of a v_i; invalidate cache *)
            let+ s', rl = if is_def then
                let+ label = C.Label.fresh in
                let insn = RA.store_to_slot ty insn ~src:v' ~dst:slot in
                Insn.create ~label ~insn :: s,
                Map.remove rl v
              else !!(s, rl) in
            (* Update the substitution. *)
            let m' = Map.set m ~key:v ~data:v' in
            (* initial := initial ∪ newTemps *)
            add_initial t v';
            (* Mark `v'` as a reload temporary so `select_spill` avoids it.
               Reload temps introduced here have short live ranges but can
               interfere with all K surviving registers at a loop use point,
               giving them cost/degree < original variables. Without this
               flag their low cost causes `select_spill` to pick them first,
               spilling them in `assign_colors` and creating an infinite cascade.
               Infinite spill cost forces original variables to be simplified
               first, dropping the reload temps below K so they move to
               `wsimplify` and get colored rather than actually spilled. *)
            t.reload_bits <- Bitset.set t.reload_bits t.$[v'];
            t.types <- Map.set t.types ~key:v' ~data:ty;
            f', s', m', rl) in
    (* Apply the substitution to the existing instruction. *)
    let subst n = Map.find subst n |> Option.value ~default:n in
    let i' = Insn.with_insn i @@ RA.substitute insn subst in
    List.iter fetch ~f:(Vec.push ivec);
    Vec.push ivec i';
    List.iter store ~f:(Vec.push ivec);
    reload

  let rewrite_blk t b blks ivec =
    let+ _rl =
      Blk.insns b |> C.Seq.fold
        ~init:Rv.Map.empty ~f:(fun rl i ->
            let insn = Insn.insn i in
            let rl = if RA.is_call insn
              then Rv.Map.empty else rl in
            if same_slot_copy t insn then !!rl
            else rewrite_insn t rl ivec i) in
    let data = Blk.with_insns b @@ Vec.to_list ivec in
    LT.set blks ~key:(Blk.label b) ~data;
    Vec.clear ivec

  module Remove_deads = Pseudo_passes.Remove_dead_insns(M)

  let rewrite_function t =
    let ivec = Vec.create () in
    let blks = LT.create ~capacity:(Func.num_blks t.fn) () in
    Func.blks t.fn |> Seq.iter ~f:(fun b ->
        LT.set blks ~key:(Blk.label b) ~data:b);
    let+ () =
      Semi_nca.Tree.preorder t.dom |>
      C.Seq.iter ~f:(fun l ->
          match LT.find blks l with
          | Some b -> rewrite_blk t b blks ivec
          | None -> !!()) in
    let fn = Func.map_blks t.fn ~f:(fun b ->
        Blk.label b |> LT.find blks |>
        Option.value ~default:b) in
    t.fn <- Remove_deads.run fn

  (* Insert spilling code and set up the state for the next round. *)
  let spill_and_reload t =
    let* () = make_slots t in
    let+ () = rewrite_function t in
    (* spilledNodes := {} *)
    t.spilled <- Bitset.empty;
    (* initial := coloredNodes ∪ coalescedNodes *)
    t.initial <- Bitset.union t.initial (Bitset.union t.colored t.coalesced);
    (* coloredNodes := {} *)
    t.colored <- Bitset.empty;
    (* coalescedNodes := {} *)
    t.coalesced <- Bitset.empty

  (* Clear the relevant state for the next round. *)
  let new_round t =
    t.data.live <- None;
    LT.clear t.copies;
    LT.clear t.insn_blks;
    Wmoves.reset t;
    Wfreeze.reset t;
    t.data.amoves <- Lset.empty;
    t.cmoves <- Lset.empty;
    t.kmoves <- Lset.empty;
    t.fmoves <- Lset.empty;
    alloc_arrays t

  let rec main t ~round ~max_rounds ~invariants =
    let* () = C.when_ (round > max_rounds) @@ fun () ->
      C.failf "In Regalloc.main: maximum rounds reached (%d) with no \
               convergence on spilling" max_rounds () in
    Logs.debug (fun m ->
        m "%s: $%s: round %d of %d"
          __FUNCTION__ (Func.name t.fn) round max_rounds);
    (* Build the interference graph. *)
    t.data.live <- Some (Live.compute ~keep:t.keep t.fn);
    let* () = build t in
    (* Override spill costs for reload temporaries. After build computes
       costs from use counts, pin every reload temp to max so `select_spill`
       never picks them preferentially over original variables. *)
    Bitset.iter t.reload_bits ~f:(fun id ->
        t.data.spill_cost.(id) <- Int.max_value);
    make_worklist t;
    (* Process the worklists. *)
    let continue = ref true in
    while !continue do
      if invariants then check_invariants t;
      if not @@ Bitset.is_empty t.wsimplify then
        simplify t
      else if not @@ Wmoves.is_empty t then
        coalesce t
      else if not @@ Wfreeze.is_empty t then
        freeze t
      else if not @@ Wspill.is_empty t then
        select_spill t
      else
        continue := false
    done;
    (* Assign colors or spill. *)
    assign_colors t;
    (* Rewrite according to the spilled nodes. *)
    C.unless (Bitset.is_empty t.spilled) @@ fun () ->
    let* () = spill_and_reload t in
    new_round t;
    main t ~round:(round + 1) ~max_rounds ~invariants

  let apply_alloc t =
    let subst rv =
      let id = t.$[rv] in
      match t.colors.(id) with
      | -1 ->
        assert (exclude_from_coloring t id);
        rv
      | c ->
        assert (can_be_colored t id);
        Rv.reg @@ match Regs.classof rv with
        | GPR -> Regs.allocatable.(c)
        | FP -> Regs.allocatable_fp.(c) in
    Func.map_blks t.fn ~f:(fun b ->
        Blk.fold_insns ~rev:true b ~init:[] ~f:(fun acc i ->
            let insn = Insn.insn i in
            let insn' = RA.substitute insn subst in
            (* Now we can remove useless copies. *)
            match RA.is_copy insn' with
            | Some (d, s) when Rv.(d = s) -> acc
            | Some _ | None -> Insn.with_insn i insn' :: acc) |>
        Blk.with_insns b)

  module Layout = Regalloc_stack_layout.Make(M)(C)

  let run ?(max_rounds = 40) ?(invariants = false) fn =
    let* fn, presize = Layout.pre_assign fn in
    assert (not @@ Func.has_any_slots fn);
    let t = create fn in
    t.fn <- fn;
    initialize t;
    let* () = main t ~round:1 ~max_rounds ~invariants in
    let fn = apply_alloc t in
    Layout.post_assign fn presize
end
