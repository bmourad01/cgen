(* Implementation of "Iterated Register Coalescing (1996)"
   by L. George and A. Appel *)

open Core
open Regular.Std
open Pseudo

module Lset = Label.Tree_set

(* Pick the first element we encounter in the set and remove it. *)
let take_one hs =
  let e = with_return @@ fun {return} ->
    Hash_set.iter hs ~f:return;
    assert false in
  Hash_set.remove hs e;
  e

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax
  open Regalloc_irc_state.Make(M)

  let ensure_degree t n =
    if can_be_colored t n then
      Hashtbl.update t.degree n ~f:(function
          | None -> 0
          | Some d -> d)

  (* Adds an edge between `u` and `v` in the interference graph. *)
  let add_edge t u v =
    (* A node cannot interfere with itself, nor a node with a different
       register class. Nodes that correspond to slots are excluded. *)
    ensure_degree t u;
    ensure_degree t v;
    if Rv.(u <> v)
    && Regs.same_class_node u v
    && not (Hashtbl.mem t.slots u)
    && not (Hashtbl.mem t.slots v) then begin
      (* We're going to combine the `adjList` and `adjSet`. *)
      add_adjlist t u v;
      add_adjlist t v u;
      (* if u \notin precolored then
           degree[u] := degree[u]+1 *)
      if can_be_colored t u then inc_degree t u;
      (* if v \notin precolored then
           degree[v] := degree[v]+1 *)
      if can_be_colored t v then inc_degree t v
    end

  let build_insn ~loop_depth t out i =
    let label = Insn.label i in 
    let insn = Insn.insn i in
    let use = M.Insn.reads insn in
    Set.iter use ~f:(update_cost ~loop_depth t);
    let def = M.Insn.writes insn in
    (* if isMoveInstruction(I) then *)
    let+ out = match M.Regalloc.is_copy insn with
      | None -> !!out
      | Some (d, s) ->
        (* This is an invariant that is required of `M.Regalloc.is_copy`; better
           to fail loudly here than silently introduce errors. *)
        let+ () = C.unless (Regs.same_class_node d s) @@ fun () ->
          C.failf "In Regalloc.build_insn: got a copy instruction `%a` between \
                   between two different register classes (%a, %a)"
            (Insn.pp M.Insn.pp) i Rv.pp d Rv.pp s () in
        (* live := live\use(I) *)
        let out = Set.diff out use in
        (* forall n \in def(I) U use(I)
             moveList[n] := moveList[n] U {I} *)
        add_move t label d;
        add_move t label s;
        Hashtbl.set t.copies ~key:label ~data:{
          dst = d;
          src = s;
          loop = loop_depth;
        };
        (* worklistMoves := worklistMoves U {I} *)
        t.wmoves <- Lset.add t.wmoves label;
        out in
    (* live := live U def(I) *)
    let out = Set.union out def in
    (* forall d \in def(I) *)
    Set.iter def ~f:(fun d ->
        (* forall l \in live
             AddEdge(l,d) *)
        Set.iter out ~f:(fun o -> add_edge t o d));
    (* live := use(I) U (live\def(I)) *)
    Set.union use (Set.diff out def)

  (* Build the interference graph and other initial state for the
     algorithm. *)
  let build t live =
    (* forall b \in blocks in program *)
    Func.blks t.fn |> C.Seq.iter ~f:(fun b ->
        let l = Blk.label b in
        let loop_depth = match Loop.blk t.loop l with
          | None -> 0
          | Some lp ->
            (* NB: levels start at 0 *)
            (Loop.(level (get t.loop lp)) :> int) + 1 in
        (* live := liveOut(b) *)
        let out = Live.outs live l in
        (* forall I \in instructions(b) in reverse order *)
        let+ _out =
          Blk.insns b ~rev:true |>
          C.Seq.fold ~init:out ~f:(build_insn ~loop_depth t) in
        ())

  (* Initialize the worklists. *)
  let make_worklist t =
    Hash_set.iter t.initial ~f:(fun n ->
        (* If we introduced `n` during spilling, but later removed
           its definition during dead code elimination, then it
           won't have a degree. *)
        degree' t n |> Option.iter ~f:(fun d ->
            if d >= Regs.node_k n then
              add_spill t n
            else if move_related t n then
              Hash_set.add t.wfreeze n
            else
              Hash_set.add t.wsimplify n));
    Hash_set.clear t.initial

  let enable_moves t nodes =
    (* forall n \in nodes *)
    Set.iter nodes ~f:(fun n ->
        (* forall m \in NodeMoves(m) *)
        node_moves t n |> Lset.iter ~f:(fun m ->
            (* if m \in activeMoves then *)
            if Lset.mem t.amoves m then begin
              (* activeMoves := activeMoves \ {m} *)
              t.amoves <- Lset.remove t.amoves m;
              (* worklistMoves := worklistMoves U {m} *)
              t.wmoves <- Lset.add t.wmoves m;
            end))

  (* Simulate removing a node grom the interference graph (this is what
     the `degree` table is for). *)
  let decrement_degree t m =
    match degree' t m with
    | None ->
      assert (exclude_from_coloring t m)
    | Some d ->
      assert (can_be_colored t m);
      (* let d = degree[m]
         degree[m] := d-1 *)
      dec_degree t m;
      (* if d = K then *)
      if d = Regs.node_k m then begin
        (* EnableMoves({m} U Adjacent(m)) *)
        enable_moves t @@ Set.add (adjacent t m) m;
        (* spillWorklist := splillWorklist \ {m} *)
        remove_spill t m;
        (* if MoveRelated(m) then
             freezeWorklist := freezeWorklist U {m}
           else
             simplifyWorklist := simplifyWorklist U {m} *)
        if move_related t m
        then Hash_set.add t.wfreeze m
        else Hash_set.add t.wsimplify m
      end

  (* pre: wsimplify is not empty *)
  let simplify t =
    (* let n \in simplifyWorklist
       simplifyWorklist := simplifyWorklist \ {n} *)
    let n = take_one t.wsimplify in
    (* push(n, selectStack) *)
    if can_be_colored t n then begin
      Logs.debug (fun m -> m "%s: selecting %a%!" __FUNCTION__ Rv.pp n);
      Stack.push t.select n;
    end;
    (* forall m \in Adjacent(n) *)
    adjacent t n |> Set.iter ~f:(decrement_degree t)

  let should_add_to_worklist t u =
    (* u \notin precolored *)
    can_be_colored t u &&
    (* not(MoveRelated(u)) *)
    not (move_related t u) &&
    (* degree[u] < K *)
    degree t u < Regs.node_k u 

  let add_worklist t u = if should_add_to_worklist t u then begin
      (* freezeWorklist := freezeWorklist \ {u} *)
      Hash_set.remove t.wfreeze u;
      (* simplifyWorklist := simplifyWorklist U {u} *)
      Hash_set.add t.wsimplify u;
    end

  let ok t a r =
    (* t \in precolored *)
    exclude_from_coloring t a ||
    (* degree[t] < K *)
    degree t a < Regs.node_k a ||
    (* (a,r) \in adjSet *)
    has_edge t a r

  (* forall t \in Adjacent(v), OK(t,u)  *)
  let all_adjacent_ok t u v =
    adjacent t v |> Set.for_all ~f:(fun a -> ok t a u)

  (* Briggs conservative coalescing heuristic.

     let k = 0
     forall n \in nodes
       if degree[n] >= k then k := k + 1
     return (k < K)
  *)
  let conservative t nk nodes =
    let k = Set.fold nodes ~init:0 ~f:(fun k n ->
        if degree t n >= Regs.node_k n then k + 1 else k) in
    k < nk

  (* Conservative(Adjacent(u) U Adjacent(v)) *)
  let conservative_adj t u v =
    assert (Regs.same_class_node u v);
    let nodes = Set.union (adjacent t u) (adjacent t v) in
    conservative t (Regs.node_k u) nodes

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
          __FUNCTION__ Rv.pp u Rv.pp v e);
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
          __FUNCTION__ Rv.pp u Rv.pp v);
    (* if v \in freezeWorklist *)
    if Hash_set.mem t.wfreeze v then
      (* freezeWorklist := freezeWorklist \ {v} *)
      Hash_set.remove t.wfreeze v
    else
      (* spillWorklist := spillWorklist \ {v} *)
      remove_spill t v;
    (* coalescedNodes := coalescedNodes U {v} *)
    Hash_set.add t.coalesced v;
    (* alias[v] := u *)
    Hashtbl.set t.alias ~key:v ~data:u;
    (* nodeMoves[u] := nodeMoves[u] U nodeMoves[v] *)
    let vm = moves t v in
    Hashtbl.update t.moves u ~f:(function
        | Some um -> Lset.union um vm
        | None -> vm);
    (* forall t \in Adjacent(v) *)
    adjacent t v |> Set.iter ~f:(combine_edge t u);
    if (* degree[u] >= K *)
      degree t u >= Regs.node_k u &&
      (* u \in freezeWorklist *)
      Hash_set.mem t.wfreeze u then begin
      (* freezeWorklist := freezeWorklist \ {u} *)
      Hash_set.remove t.wfreeze u;
      (* spillWorklist := spillWorklist U {u} *)
      add_spill t u
    end

  (* P(u,v) = S(u,v) * (W(u,v) / (1 + D'(u) + D'(v)))

     where:
     - S is the "safety factor"
     - W is the "weight" of the move
     - D' is the "effective degree"

     W follows our heuristic for spill priority: 10^loop_depth
  *)
  let move_priority t m =
    let c = Hashtbl.find_exn t.copies m in
    let pu = exclude_from_coloring t c.dst in
    let pv = exclude_from_coloring t c.src in
    if pu && pv then 0.0 else
      (* Pre-colored nodes don't actually have a degree, so we need to scale
         the result such that a node with degree > K doesn't outweigh a node
         that is pre-colored. *)
      let effective_degree n p =
        let k = Regs.node_k n in
        let k' = k * 2 in
        if p then k' else
          let d = degree t n in
          if d <= k then d else
            (* If `d > K`, then we're OK with scaling off the tail end
               towards our threshold of 2K, since such nodes are effectively
               uncolorable until we allow `simplify` to make progress. *)
            min (k' - 1) (k + ((d - k) / 2)) in
      let du = effective_degree c.dst pu in
      let dv = effective_degree c.src pv in
      let w = Float.of_int @@ Int.pow 10 c.loop in
      let p = w /. Float.of_int (1 + du + dv) in
      (* If one of the nodes is pre-colored, then this coalesce will be
         much riskier. If both are pre-colored, then we should avoid it
         at all costs (see topmost condition). *)
      if pu || pv then p *. 0.25 else p

  (* Pick a move from the worklist that would profit the most from
     coalescing. *)
  let pick_move t =
    Lset.to_sequence t.wmoves |>
    Seq.map ~f:(fun m -> m, move_priority t m) |>
    Seq.max_elt ~compare:(fun (_, a) (_, b) ->  Float.compare a b) |>
    Option.value_exn

  (* pre: wmoves is not empty *)
  let coalesce t =
    (* let m_(=copy(x,y)) \in worklistMoves *)
    let m, score = pick_move t in
    let c = Hashtbl.find_exn t.copies m in
    (* x := GetAlias(x) *)
    let x = alias t c.dst in
    (* y := GetAlias(y) *)
    let y = alias t c.src in
    (* if y \in precolored then
         let (u,v) = (y,x)
       else
         let (u,v) = (x,y) *)
    let u, v = if exclude_from_coloring t y then y, x else x, y in
    Logs.debug (fun m_ ->
        m_ "%s: looking at move %a, score=%g, u=%a, v=%a%!"
          __FUNCTION__ Label.pp m score Rv.pp u Rv.pp v);
    (* worklistMoves := worklistMoves \ {m} *)
    t.wmoves <- Lset.remove t.wmoves m;
    (* if u = v then *)
    if Rv.(u = v) then begin
      (* coalescedMoves := coalescedMoves U {m} *)
      t.cmoves <- Lset.add t.cmoves m;
      (* AddWorkList(u) *)
      add_worklist t u
    end else if
      (* v \in precolored *)
      exclude_from_coloring t v ||
      (* (u,v) \in adjSet *)
      has_edge t u v then begin
      Logs.debug (fun m_ ->
          m_ "%s: constraining %a%!" __FUNCTION__ Label.pp m);
      (* constrainedMoves := constrainedMoves U {m} *)
      t.kmoves <- Lset.add t.kmoves m;
      (* addWorkList(u) *)
      add_worklist t u;
      (* addWorkList(v) *)
      add_worklist t v
    end else if
      (* u \in precolored ^ (\forall t \in Adjacent(v), OK(t,u)) *)
      (exclude_from_coloring t u && all_adjacent_ok t u v) ||
      (* u \notin precolored ^ Conservative(Adjacent(u), Adjacent(v)) *)
      (can_be_colored t u && conservative_adj t u v) then begin
      (* coalescedMoves := coalescedMoves U {m} *)
      t.cmoves <- Lset.add t.cmoves m;
      (* Combine(u,v) *)
      combine t u v;
      (* AddWorkList(u) *)
      add_worklist t u
    end else
      (* activeMoves := activeMoves U {m} *)
      t.amoves <- Lset.add t.amoves m

  (* pre: m \in copies

     Returns the other node `v` of the copy.
  *)
  let uvcopy t u m =
    let c = Hashtbl.find_exn t.copies m in
    if Rv.(c.dst = u) then Some c.src
    else if Rv.(c.src = u) then Some c.dst
    else None

  let freeze_moves t u =
    (* forall m(= copy(u,v) or copy(v,u)) \in NodeMoves(u) *)
    node_moves t u |> Lset.iter ~f:(fun m ->
        (* Check that the copy fits the schema above. *)
        uvcopy t u m |> Option.iter ~f:(fun v ->
            (* if m \in activeMoves *)
            if Lset.mem t.amoves m then
              (* activeMoves := activeMoves \ {m} *)
              t.amoves <- Lset.remove t.amoves m 
            else
              (* worklistMoves := worklistMoves \ {m} *)
              t.wmoves <- Lset.remove t.wmoves m;
            (* frozenMoves := frozenMoves U {m} *)
            Logs.debug (fun m_ ->
                m_ "%s: freezing move %a, v=%a"
                  __FUNCTION__ Label.pp m Rv.pp v);
            t.fmoves <- Lset.add t.fmoves m;
            (* if NodeMoves(v) = {} ^ degree[v] < K *)
            if Lset.is_empty (node_moves t v)
            && degree t v < Regs.node_k v then begin
              (* freezeWorklist := freezeWorklist \ {v} *)
              Hash_set.remove t.wfreeze v;
              (* simplifyWorklist := simplifyWorklist U {v} *)
              Hash_set.add t.wsimplify v;
            end))

  (* pre: wfreeze is not empty *)
  let freeze t =
    (* let u \in freezeWorklist
       freezeWorklist := freezeWorklist \ {u} *)
    let u = take_one t.wfreeze in
    Logs.debug (fun m -> m "%s: frozen node u=%a%!" __FUNCTION__ Rv.pp u);
    (* simplifyWorklist := simplifyWorklist U {u} *)
    Hash_set.add t.wsimplify u;
    (* FreezeMoves(u) *)
    freeze_moves t u

  let select_spill t =
    Pairing_heap.pop t.wspill |> Option.iter ~f:(fun m ->
        Logs.debug (fun m_ ->
            m_ "%s: selecting spill node %a%!"
              __FUNCTION__ Rv.pp m);
        (* spillWorklist := spillWorklist \ {m} *)
        Hashtbl.remove t.wspill_elts m;
        (* simplifyWorklist := simplifyworklist U {m} *)
        Hash_set.add t.wsimplify m;
        (* FreezeMoves(m) *)
        freeze_moves t m)

  (* For all neighbors of `n` that have a color, remove them from the
     set of his available colors. *)
  let eliminate_colors t n cs =
    (* forall w \in adjList[n] *)
    adjlist t n |> Set.to_sequence |> Seq.map ~f:(alias t) |>
    (* if GetAlias(w) \in (coloredNodes U precolored) then *)
    Seq.filter ~f:(fun w -> Rv.is_reg w || Hash_set.mem t.colored w) |>
    (* okColors := okColors \ {color[GetAlias(w)]} *)
    Seq.filter_map ~f:(color t) |>
    Seq.iter ~f:(fun c -> cs := Z.(!cs land ~!(one lsl c)))

  let assign_colors t =
    (* while SelectStack is not empty
       let n = pop(SelectStack) *)
    Stack.until_empty t.select (fun n ->
        assert (can_be_colored t n);
        (* okColors := {0,...,K-1} *)
        let k = Regs.node_k n in
        let cs = ref Z.(pred (one lsl k)) in
        eliminate_colors t n cs;
        (* if okColors = {} then *)
        if Z.(equal !cs zero) then
          (* spilledNodes := spilledNodes U {n} *)
          t.spilled <- Set.add t.spilled n
        else begin
          (* coloredNodes := coloredNodes U {n} *)
          Hash_set.add t.colored n;
          (* let c \in okColors
             color[n] := c *)
          set_color t n @@ Z.trailing_zeros !cs
        end);
    (* forall n \in coalescedNodes *)
    Hash_set.iter t.coalesced ~f:(fun n ->
        (* color[n] := color[GetAlias(n)] *)
        alias t n |> color t |> Option.iter ~f:(set_color t n))

  let typeof t v = match Map.find t.types v with
    | None -> C.failf "no type available for spilled node %a" Rv.pp v ()
    | Some ty -> !!ty

  (* Find an existing slot of comparable size that doesn't interfere
     with `n`. *)
  let find_reusable_slot t m n size =
    Map.find m size |> Option.bind ~f:(fun vs ->
        List.find vs ~f:(Fn.non @@ has_edge t n))

  (* Create slots for spilled nodes. *)
  let make_slots t =
    let+ slots, _ =
      Set.to_sequence t.spilled |>
      C.Seq.fold ~init:([], Int.Map.empty) ~f:(fun (acc, m) n ->
          match Rv.which n with
          | First _ -> assert false
          | Second (v, _) ->
            let+ size = typeof t n >>| function
              | #Type.basic as b -> Type.sizeof_basic b / 8
              | `v128 -> 16 in
            let r = Rv.var GPR v in
            match find_reusable_slot t m n size with
            | Some r' ->
              Logs.debug (fun m ->
                  m "%s: re-using slot %a for spilled node %a%!"
                    __FUNCTION__ Rv.pp r' Rv.pp r);
              Hashtbl.set t.slots ~key:r ~data:r';
              acc, m
            | None ->
              Logs.debug (fun m ->
                  m "%s: spilling %a to new slot%!"
                    __FUNCTION__ Rv.pp r);
              let s = Virtual.Slot.create_exn v ~size ~align:size in
              Hashtbl.set t.slots ~key:r ~data:r;
              s :: acc, Map.add_multi m ~key:size ~data:r) in
    t.fn <- Func.insert_slots t.fn slots

  (* Rewrite a single instruction to spill and reload variables.

     Suppose we have:

       mov v, [v+16]

     We will transform this code to:

       mov v_i, [v]
       mov v_i, [v_i+16]
       mov [v], v_i

     Again suppose:

       mov v, [a+16]
       ...
       add a, v

     We get:

       mov v_i, [a+16]
       mov [v], v_i
       ...
       mov v_i', [v]
       add a, v_i'

     NB: `acc` is accumulated in reverse, and we populate `initial`
     with the fresh temporaries (`newTemps`) here.
  *)
  let rewrite_insn t reload ivec i =
    let insn = Insn.insn i in
    let use = M.Insn.reads insn in
    let def = M.Insn.writes insn in
    let+ fetch, store, subst, reload =
      let init = [], [], Rv.Map.empty, reload in
      Set.union use def |> Set.inter t.spilled |> Set.to_sequence |>
      C.Seq.fold ~init ~f:(fun (f, s, m, rl) v ->
          let* ty = typeof t v in
          let slot = Hashtbl.find_exn t.slots v in
          (* Create a new temporary v_i for each definition and
             each use. *)
          let* v' = C.Var.fresh >>| Rv.var (Regs.classof v) in
          (* a fetch before each use of a v_i *)
          let* f', rl = if Set.mem use v then
              let+ label = C.Label.fresh in
              let insn = match Map.find reload v with
                | None -> M.Regalloc.load_from_slot ty ~dst:v' ~src:slot
                | Some v'' -> M.Regalloc.move ty ~dst:v' ~src:v'' in
              Insn.create ~label ~insn :: f,
              Map.set rl ~key:v ~data:v'
            else !!(f, rl) in
          (* Insert a store after each definition of a v_i, *)
          let+ s', rl = if Set.mem def v then
              let+ label = C.Label.fresh in
              let insn = M.Regalloc.store_to_slot ty insn ~src:v' ~dst:slot in
              Insn.create ~label ~insn :: s,
              Map.set rl ~key:v ~data:v'
            else !!(s, rl) in
          (* Update the substitution. *)
          let m' = Map.set m ~key:v ~data:v' in
          (* initial := initial U newTemps *)
          Hash_set.add t.initial v';
          t.types <- Map.set t.types ~key:v' ~data:ty;
          f', s', m', rl) in
    (* Apply the substitution to the existing instruction. *)
    let subst n = Map.find subst n |> Option.value ~default:n in
    let i' = Insn.with_insn i @@ M.Regalloc.substitute insn subst in
    List.iter fetch ~f:(Vec.push ivec);
    Vec.push ivec i';
    List.iter store ~f:(Vec.push ivec);
    reload

  let rewrite_blk t b blks ivec =
    let+ _rl =
      Blk.insns b |> C.Seq.fold
        ~init:Rv.Map.empty ~f:(fun rl i ->
            let insn = Insn.insn i in
            let rl = if M.Regalloc.is_call insn
              then Rv.Map.empty else rl in
            rewrite_insn t rl ivec i) in
    let data = Blk.with_insns b @@ Vec.to_list ivec in
    Hashtbl.set blks ~key:(Blk.label b) ~data;
    Vec.clear ivec

  module Remove_deads = Pseudo_passes.Remove_dead_insns(M)

  let rewrite_function t =
    let ivec = Vec.create () in
    let blks = Label.Table.create () in
    Func.blks t.fn |> Seq.iter ~f:(fun b ->
        Hashtbl.set blks ~key:(Blk.label b) ~data:b);
    let rec loop q = match Stack.pop q with
      | None -> !!()
      | Some l ->
        let* () = match Hashtbl.find blks l with
          | Some b -> rewrite_blk t b blks ivec
          | None -> !!() in
        Semi_nca.Tree.children t.dom l |> Seq.iter ~f:(Stack.push q);
        loop q in
    let+ () = loop @@ Stack.singleton Label.pseudoentry in
    let fn = Func.map_blks t.fn ~f:(fun b ->
        Blk.label b |> Hashtbl.find blks |>
        Option.value ~default:b) in
    t.fn <- Remove_deads.run fn

  (* Insert spilling code and set up the state for the next round. *)
  let spill_and_reload t =
    let* () = make_slots t in
    let+ () = rewrite_function t in
    (* spilledNodes := {} *)
    t.spilled <- Rv.Set.empty;
    (* initial := coloredNodes U coalescedNodes *)
    Hash_set.iter t.colored ~f:(Hash_set.add t.initial);
    Hash_set.iter t.coalesced ~f:(Hash_set.add t.initial);
    (* coloredNodes := {} *)
    Hash_set.clear t.colored;
    (* coalescedNodes := {} *)
    Hash_set.clear t.coalesced

  (* Clear the relevant state for the next round. *)
  let new_round t =
    Hashtbl.clear t.adjlist;
    Hashtbl.clear t.degree;
    Hashtbl.clear t.copies;
    Hashtbl.clear t.moves;
    Hashtbl.clear t.spill_cost;
    (* This doesn't seem to happen in the paper, but we should discard
       the previous coloring since we introduced new spill/reload code.

       Since `rewrite_program` will add the colored and coalesced nodes
       to the `initial` set, this should be safe as some if not all of
       them can make their way to `simplify`.
    *)
    Hashtbl.clear t.colors

  let rec main t ~round ~max_rounds =
    let* () = C.when_ (round > max_rounds) @@ fun () ->
      C.failf "In Regalloc.main: maximum rounds reached (%d) with no \
               convergence on spilling" max_rounds () in
    Logs.debug (fun m ->
        m "%s: $%s: round %d of %d"
          __FUNCTION__ (Func.name t.fn) round max_rounds);
    (* Build the interference graph. *)
    let live = Live.compute ~keep:t.keep t.fn in
    let* () = build t live in
    make_worklist t;
    (* Process the worklists. *)
    let continue = ref true in
    while !continue do
      if not @@ Hash_set.is_empty t.wsimplify then
        simplify t
      else if not @@ Lset.is_empty t.wmoves then
        coalesce t
      else if not @@ Hash_set.is_empty t.wfreeze then
        freeze t
      else if not @@ Pairing_heap.is_empty t.wspill then
        select_spill t
      else
        continue := false
    done;
    (* Assign colors or spill. *)
    assign_colors t;
    (* Rewrite according to the spilled nodes. *)
    C.unless (Set.is_empty t.spilled) @@ fun () ->
    let* () = spill_and_reload t in
    new_round t;
    main t ~round:(round + 1) ~max_rounds

  let apply_alloc t =
    let subst n = match Hashtbl.find t.colors n with
      | None ->
        assert (exclude_from_coloring t n); n
      | Some c ->
        assert (can_be_colored t n);
        Rv.reg @@ match Regs.classof n with
        | GPR -> Regs.allocatable.(c)
        | FP -> Regs.allocatable_fp.(c) in
    Func.map_blks t.fn ~f:(fun b ->
        Blk.insns b |> Seq.filter_map ~f:(fun i ->
            let insn = Insn.insn i in
            let insn' = M.Regalloc.substitute insn subst in
            (* Now we can remove useless copies. *)
            match M.Regalloc.is_copy insn' with
            | Some (d, s) when Rv.(d = s) -> None
            | Some _ | None -> Some (Insn.with_insn i insn')) |>
        Seq.to_list |> Blk.with_insns b)

  module Layout = Regalloc_stack_layout.Make(M)(C)

  let run ?(max_rounds = 40) fn =
    let* fn, presize = Layout.pre_assign fn in
    assert (Seq.is_empty @@ Func.slots fn);
    let t = create fn in
    t.fn <- fn;
    init_initial t;
    let* () = main t ~round:1 ~max_rounds in
    let fn = apply_alloc t in
    Layout.post_assign fn presize
end
