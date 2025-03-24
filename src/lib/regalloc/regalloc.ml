(* Implementation of "Iterated Register Coalescing (1996)"
   by L. George and A. Appel *)

open Core
open Regular.Std
open Graphlib.Std
open Pseudo

module Lset = Label.Tree_set

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  (* Enforce the invariant that the scratch register for each
     class may not appear in the allocatable registers. *)
  let () =
    List.iter M.Reg.allocatable ~f:(fun r ->
        assert (not M.Reg.(equal r scratch));
        assert (not M.Reg.(equal r sp));
        assert (not M.Reg.(equal r fp));
        match M.Reg.classof r with
        | `fp -> assert false
        | `gpr -> ());
    List.iter M.Reg.allocatable_fp ~f:(fun r ->
        assert (not M.Reg.(equal r scratch_fp));
        match M.Reg.classof r with
        | `gpr -> assert false
        | `fp -> ())

  module Rv = M.Regvar
  module G = Graphlib.Make(Rv)(Unit)
  module Live = Live(M)

  let classof rv = match Rv.which rv with
    | First r -> M.Reg.classof r
    | Second (_, k) -> k

  let same_class k k' = match k, k' with
    | `gpr, `gpr -> true
    | `fp, `fp -> true
    | _ -> false

  let same_class_node a b = same_class (classof a) (classof b)

  let allocatable = Array.of_list M.Reg.(scratch :: allocatable)
  let allocatable_fp = Array.of_list M.Reg.(scratch_fp :: allocatable_fp)

  let kallocatable = Array.length allocatable
  let kallocatable_fp = Array.length allocatable_fp

  let prealloc =
    let t = Hashtbl.create (module M.Reg) in
    Array.iteri allocatable ~f:(fun i r ->
        Hashtbl.add_exn t ~key:r ~data:i);
    t

  let prealloc_fp =
    let t = Hashtbl.create (module M.Reg) in
    Array.iteri allocatable_fp ~f:(fun i r ->
        Hashtbl.add_exn t ~key:r ~data:i);
    t

  let () = assert (Hashtbl.find_exn prealloc M.Reg.scratch = 0)
  let () = assert (Hashtbl.find_exn prealloc_fp M.Reg.scratch_fp = 0)
  let scratch_inv_mask = Z.(~!one)

  let reg_color r =
    let tbl = match M.Reg.classof r with
      | `gpr -> prealloc
      | `fp -> prealloc_fp in
    Hashtbl.find tbl r

  (* The number of allocatable registers for a given register class. *)
  let class_k = function
    | `gpr -> kallocatable
    | `fp -> kallocatable_fp

  (* Choose K based on the register class. `initial` should
     not contain pre-colored nodes. *)
  let node_k n = class_k @@ classof n

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
    mutable fn     : (M.Insn.t, M.Reg.t) func;
    mutable g      : G.t;
    degree         : int Rv.Table.t;
    moves          : Lset.t Rv.Table.t;
    copies         : (Rv.t * Rv.t) Label.Table.t;
    mutable wmoves : Lset.t; (* worklist moves *)
    mutable amoves : Lset.t; (* active moves *)
    mutable cmoves : Lset.t; (* coalesced moves *)
    mutable kmoves : Lset.t; (* constrained moves *)
    mutable fmoves : Lset.t; (* frozen moves *)
    wspill         : Rv.Hash_set.t;
    wfreeze        : Rv.Hash_set.t;
    wsimplify      : Rv.Hash_set.t;
    coalesced      : Rv.Hash_set.t;
    spilled        : Rv.Hash_set.t;
    colored        : Rv.Hash_set.t;
    initial        : Rv.Hash_set.t;
    slots          : Rv.Hash_set.t;
    colors         : int Rv.Table.t;
    select         : Rv.t Stack.t;
    alias          : Rv.t Rv.Table.t;
    keep           : Rv.Set.t;
  } [@@ocaml.warning "-69"]

  (* Set of registers that should always be live at the exit. *)
  let init_keep fn =
    let init = Rv.Set.singleton @@ Rv.reg M.Reg.sp in
    Func.rets fn |> Seq.map ~f:Rv.reg |> Seq.fold ~init ~f:Set.add

  let create fn = {
    fn;
    g = G.empty;
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
    spilled = Rv.Hash_set.create ();
    colored = Rv.Hash_set.create ();
    initial = Rv.Hash_set.create ();
    slots = Rv.Hash_set.create ();
    colors = Rv.Table.create ();
    select = Stack.create ();
    alias = Rv.Table.create ();
    keep = init_keep fn;
  }

  let inc_degree t n =
    Hashtbl.update t.degree n ~f:(function
        | Some d -> d + 1
        | None -> 1)

  let dec_degree t n =
    Hashtbl.update t.degree n ~f:(function
        | Some d -> max 0 (d - 1)
        | None -> 0)

  (* All variables should be in this table. Preassigned registers
     won't be in here, so they should just get the maximum value. *)
  let degree t n =
    Hashtbl.find t.degree n |>
    Option.value ~default:Int.max_value

  (* Mimic the adjList *)
  let adjlist t n = if Rv.is_var n then G.Node.succs n t.g else Seq.empty
  let adjlist_set t n = Rv.Set.of_sequence @@ adjlist t n

  (* adjList[n] \ (selectStack U coalescedNodes) *)
  let adjacent t n =
    let a = adjlist_set t n in
    let a = Stack.fold t.select ~init:a ~f:Set.remove in
    Hash_set.fold t.coalesced ~init:a ~f:Set.remove

  let moves t n = match Hashtbl.find t.moves n with
    | None -> Lset.empty
    | Some m -> m

  (* moveList[n] /\ (activeMoves U worklistMoves) *)
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
    | First r -> reg_color r

  let set_color t n c = Hashtbl.set t.colors ~key:n ~data:c

  (* Adds an edge between `u` and `v` in the interference graph.

     Note that we don't use the adjList like in the paper, but instead
     we use a filter on the adjSet.
  *)
  let add_edge t u v =
    (* A node cannot interfere with itself, nor a node with a different
       register class. Nodes that correspond to slots are excluded. *)
    if Rv.(u <> v)
    && same_class_node u v
    && not (Hash_set.mem t.slots u)
    && not (Hash_set.mem t.slots v) then
      (* adjSet := adjSet U {(u,v),(v,u)} *)
      let uv = G.Edge.create u v () in
      let vu = G.Edge.create v u () in
      t.g <- G.Edge.(insert uv (insert vu t.g));
      (* if u \notin precolored then
           degree[u] := degree[u]+1 *)
      if Rv.is_var u then inc_degree t u;
      (* if v \notin precolored then
           degree[v] := degree[v]+1 *)
      if Rv.is_var v then inc_degree t v

  let add_move t label n =
    Hashtbl.update t.moves n ~f:(function
        | None -> Lset.singleton label
        | Some ls -> Lset.add ls label)

  let build_insn t out i =
    let label = Insn.label i in 
    let insn = Insn.insn i in
    let use = M.Insn.reads insn in
    let def = M.Insn.writes insn in
    (* if isMoveInstruction(I) then *)
    let out = match M.Insn.copy insn with
      | None -> out
      | Some ((d, s) as p) ->
        (* This is an invariant that is required of `M.Insn.copy`; better
           to fail loudly here than silently introduce errors. *)
        assert (same_class_node d s);
        (* live := live\use(I) *)
        let out = Set.diff out use in
        (* forall n \in def(I) U use(I)
             moveList[n] := moveList[n] U {I} *)
        add_move t label d;
        add_move t label s;
        Hashtbl.set t.copies ~key:label ~data:p;
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
    (* live := use(I) U (live\def(I))  *)
    Set.union use (Set.diff out def)

  let build_blk t live b =
    let out = Live.outs live @@ Blk.label b in
    let _ =
      Blk.insns b ~rev:true |>
      Seq.fold ~init:out ~f:(build_insn t) in
    ()

  let build t live =
    (* Reset state that gets computed during `build_blk` and `build_insn`. *)
    Hashtbl.clear t.degree;
    Hashtbl.clear t.copies;
    Hashtbl.clear t.moves;
    t.g <- G.empty;
    (* Build the interference graph. *)
    Func.blks t.fn |> Seq.iter ~f:(build_blk t live);
    (* Initialize the worklists. *)
    Hash_set.iter t.initial ~f:(fun n ->
        if degree t n >= node_k n then
          Hash_set.add t.wspill n
        else if move_related t n then
          Hash_set.add t.wfreeze n
        else
          Hash_set.add t.wsimplify n);
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

  let decrement_degree t adj m =
    (* let d = degree[m]
       degree[m] := d-1 *)
    let d = degree t m in
    dec_degree t m;
    (* if d = K then *)
    if d = node_k m then begin
      (* EnableMoves({m} U Adjacent(m)) *)
      enable_moves t @@ Set.add adj m;
      (* spillWorklist := splillWorklist \ {m} *)
      Hash_set.remove t.wspill m;
      (* if MoveRelated(m) then
           freezeWorklist := freezeWorklist U {m}
         else
           simplifyWorklist := simplifyWorklist U {m} *)
      if move_related t m
      then Hash_set.add t.wfreeze m
      else Hash_set.add t.wsimplify m
    end

  exception Found_node of Rv.t

  (* Pick the first element we encounter in the set. *)
  let pick hs = try
      Hash_set.iter hs ~f:(fun n -> raise_notrace @@ Found_node n);
      assert false
    with Found_node n -> n

  (* pre: wsimplify is not empty *)
  let simplify t =
    (* let n \in simplifyWorklist *)
    let n = pick t.wsimplify in
    (* simplifyWorklist := simplifyWorklist \ {n} *)
    Hash_set.remove t.wsimplify n;
    (* push(n, selectStack) *)
    Stack.push t.select n;
    (* forall m \in Adjacent(n) *)
    let adj = adjacent t n in
    Set.iter adj ~f:(decrement_degree t adj)

  let should_add_to_worklist t u =
    (* u \notin precolored *)
    Rv.is_var u && 
    (* not(MoveRelated(u)) *)
    not (move_related t u) &&
    (* degree[u] < K *)
    degree t u < node_k u 

  let add_worklist t u = if should_add_to_worklist t u then begin
      (* freezeWorklist := freezeWorklist \ {u} *)
      Hash_set.remove t.wfreeze u;
      (* simplifyWorklist := simplifyWorklist U {u} *)
      Hash_set.add t.wsimplify u;
    end

  let ok t a r =
    (* t \in precolored *)
    Rv.is_reg a ||
    (* degree[t] < K *)
    degree t a < node_k a ||
    (* (a,r) \in adjSet *)
    G.Edge.(mem (create a r ()) t.g)

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
        if degree t n >= node_k n then k + 1 else k) in
    k < nk

  (* Conservative(Adjacent(u) U Adjacent(v)) *)
  let conservative_adj t u v =
    assert (same_class_node u v);
    let nodes = Set.union (adjacent t u) (adjacent t v) in
    conservative t (node_k u) nodes

  (* Combine `v` with `u` in the interference graph, where
     `u` is the destination. *)
  let combine t u v =
    (* if v \in freezeWorklist *)
    if Hash_set.mem t.wfreeze v then
      (* freezeWorklist := freezeWorklist \ {u} *)
      Hash_set.remove t.wfreeze v
    else
      Hash_set.remove t.wspill v;
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
    let adj = adjacent t v in
    Set.iter adj ~f:(fun a ->
        (* AddEdge(t,u) *)
        add_edge t a u;
        (* DecrementDegree(t) *)
        decrement_degree t adj a);
    if (* degree[u] >= K*)
      degree t u >= node_k u &&
      (* u \in freezeWorklist *)
      Hash_set.mem t.wfreeze u then begin
      (* freezeWorklist := freezeWorklist \ {u} *)
      Hash_set.remove t.wfreeze u;
      (* spillWorklist := spillWorklist U {u} *)
      Hash_set.add t.wspill u;
    end      

  (* pre: wmoves is not empty *)
  let coalesce t =
    (* let m_(=copy(x,y)) \in worklistMoves *)
    let m = Lset.to_sequence t.wmoves |> Seq.hd_exn in
    let x, y = Hashtbl.find_exn t.copies m in
    (* x := GetAlias(x) *)
    let x = alias t x in
    (* y := GetAlias(y) *)
    let y = alias t y in
    (* if y \in precolored then
         let (u,v) = (y,x)
       else
         let (u,v) = (x,y) *)
    let u, v = if Rv.is_reg y then y, x else x, y in
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
      Rv.is_reg v ||
      (* (u,v) \in adjSet *)
      G.Edge.(mem (create u v ()) t.g) then begin
      (* constrainedMoves := constrainedMoves U {m} *)
      t.kmoves <- Lset.add t.kmoves m;
      (* addWorkList(u) *)
      add_worklist t u;
      (* addWorkList(v) *)
      add_worklist t v
    end else if
      (* u \in precolored /\ (\forall t \in Adjacent(v), OK(t,u)) *)
      (Rv.is_reg u && all_adjacent_ok t u v) ||
      (* u \notin precolored /\ Conservative(Adjacent(u), Adjacent(v)) *)
      (Rv.is_var u && conservative_adj t u v) then begin
      (* coalescedMoves := coalescedMoves U {m} *)
      t.cmoves <- Lset.add t.cmoves m;
      (* Combine(u,v) *)
      combine t u v;
      (* AddWorkList(u) *)
      add_worklist t u
    end else
      (* activeMoves := activeMoves U {m} *)
      t.amoves <- Lset.add t.amoves m

  (* pre: u \in copies

     Returns the other node `v` of the copy.
  *)
  let uvcopy t u m =
    let d, s = Hashtbl.find_exn t.copies m in
    if Rv.(d = u) then Some s
    else if Rv.(s = u) then Some d
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
              t.wmoves <- Lset.add t.wmoves m;
            (* frozenMoves := frozenMoves U {m} *)
            t.fmoves <- Lset.add t.fmoves m;
            (* if NodeMoves(v) = {} /\ degree[v] < K *)
            if Lset.is_empty (node_moves t v)
            && degree t v < node_k v then begin
              (* freezeWorklist := freezeWorklist \ {v} *)
              Hash_set.remove t.wfreeze v;
              (* simplifyWorklist := simplifyWorklist U {v} *)
              Hash_set.add t.wsimplify v;
            end))

  (* pre: wfreeze is not empty *)
  let freeze t =
    (* let u \in freezeWorklist *)
    let u = pick t.wfreeze in
    (* freezeWorklist := freezeWorklist \ {u} *)
    Hash_set.remove t.wfreeze u;
    (* simplifyWorklist := simplifyWorklist U {u} *)
    Hash_set.add t.wsimplify u;
    (* FreezeMoves(u) *)
    freeze_moves t u

  let select_spill t =
    (* XXX: try a better heuristic as the paper suggests. For now,
       we will choose the node with the highest degree. In much of
       the literature, the spill cost is inversely proportional to
       the degree of the node. *)
    let compare a b = Int.compare (degree t a) (degree t b) in
    (* let m \in spillWorklist *)
    Hash_set.max_elt t.wspill ~compare |> Option.iter ~f:(fun m ->
        (* spillWorklist := spillWorklist \ {m} *)
        Hash_set.remove t.wspill m;
        (* simplifyWorklist := simplifyworklist U {m} *)
        Hash_set.add t.wsimplify m;
        (* FreezeMoves(m) *)
        freeze_moves t m)

  (* For all neighbors of `n` that have a color, remove them from the
     set of his available colors. *)
  let eliminate_colors t n cs =
    (* forall w \in adjList[n] *)
    adjlist t n |> Seq.map ~f:(alias t) |>
    (* if GetAlias(w) \in (coloredNodes U precolored) then *)
    Seq.filter ~f:(fun w -> Rv.is_reg w || Hash_set.mem t.colored w) |>
    (* okColors := okColors \ {color[GetAlias(w)]} *)
    Seq.filter_map ~f:(color t) |>
    Seq.iter ~f:(fun c -> cs := Z.(!cs land ~!(one lsl c)))

  (* Assign a color to `n` if possible, spilling it otherwise. *)
  let color_node t n =
    if Rv.is_var n then
      (* okColors := {0,...,K-1} *)
      let k = node_k n in
      let cs = ref Z.(pred (one lsl k)) in
      cs := Z.(!cs land scratch_inv_mask);
      eliminate_colors t n cs;
      (* if okColors = {} then *)
      if Z.(equal !cs zero) then
        (* spilledNodes := spilledNodes U {n} *)
        Hash_set.add t.spilled n
      else begin
        (* coloredNodes := coloredNodes U {n} *)
        Hash_set.add t.colored n;
        (* let c \in okColors
           color[n] := c *)
        set_color t n @@ Z.trailing_zeros !cs
      end

  let assign_colors t =
    (* while SelectStack is not empty
       let n = pop(SelectStack) *)
    Stack.until_empty t.select (color_node t);
    (* forall n \in coalescedNodes *)
    Hash_set.iter t.coalesced ~f:(fun n ->
        (* color[n] := color[GetAlias(n)] *)
        alias t n |> color t |> Option.iter ~f:(set_color t n))

  (* Create slots for spilled nodes. *)
  let make_slots t =
    let ty = Target.word M.target in
    let size = Type.sizeof_imm_base ty in
    let slots = Hash_set.fold t.spilled ~init:[] ~f:(fun acc n ->
        match Rv.which n with
        | First _ -> assert false
        | Second (v, _) ->
          let s = Virtual.Slot.create_exn v ~size ~align:size in
          Hash_set.add t.slots @@ Rv.var `gpr v;
          s :: acc) in
    t.fn <- Func.insert_slots t.fn slots

  (* Rewrite a single instruction to spill and reload variables.

     NB: `acc` is accumulated in reverse
  *)
  let rewrite_insn t acc i =
    let open C.Syntax in
    let insn = Insn.insn i in
    let use = M.Insn.reads insn in
    let def = M.Insn.writes insn in
    let+ fetch, store, subst =
      Set.union use def |> Set.to_sequence |>
      Seq.filter ~f:(Hash_set.mem t.spilled) |>
      C.Seq.fold ~init:([], [], Rv.Map.empty)
        ~f:(fun (f, s, m) v ->
            (* Create a new temporary v_i for each definition and
               each use. *)
            let* v' = C.Var.fresh >>| Rv.var (classof v) in
            (* Insert a store after each definition of a v_i, *)
            let* s' = if Set.mem def v then
                let+ label = C.Label.fresh in
                let insn = M.Regalloc.store_to_slot ~src:v' ~dst:v in
                Insn.create ~label ~insn :: s
              else !!s in
            (* a fetch before each use of a v_i *)
            let+ f' = if Set.mem use v then
                let+ label = C.Label.fresh in
                let insn = M.Regalloc.load_from_slot ~dst:v' ~src:v in
                Insn.create ~label ~insn :: f
              else !!f in
            (* Update the substitution. *)
            let m' = Map.set m ~key:v ~data:v' in
            Hash_set.add t.initial v';
            f', s', m') in
    (* Apply the substitution to the existing instruction. *)
    let subst n = Map.find subst n |> Option.value ~default:n in
    let i' = Insn.with_insn i @@ M.Regalloc.substitute insn subst in
    List.concat [fetch; i' :: store; acc]

  (* Rewrite the function to have the necessary spill code. *)
  let rewrite_function t =
    let open C.Syntax in
    let+ blks =
      Func.blks ~rev:true t.fn |>
      C.Seq.fold ~init:[] ~f:(fun acc b ->
          let+ insns =
            Blk.insns ~rev:true b |>
            C.Seq.fold ~init:[] ~f:(rewrite_insn t) in
          Blk.with_insns b insns :: acc) in
    t.fn <- Func.with_blks t.fn blks

  (* Rewrite the program for the spilled variables.

     NB: `newTemps` is added to `initial` in `rewrite_insn`.
  *)
  let rewrite_program t =
    let open C.Syntax in
    make_slots t;
    let+ () = rewrite_function t in
    (* spilledNodes := {} *)
    Hash_set.clear t.spilled;
    (* initial := coloredNodes U coalescedNodes U newTemps *)
    Hash_set.iter t.colored ~f:(Hash_set.add t.initial);
    Hash_set.iter t.coalesced ~f:(Hash_set.add t.initial);
    (* coloredNodes := {} *)
    Hash_set.clear t.colored;
    (* coalescedNodes := {} *)
    Hash_set.clear t.coalesced

  let should_stop t =
    Hash_set.is_empty t.wsimplify &&
    Lset.is_empty t.wmoves &&
    Hash_set.is_empty t.wfreeze &&
    Hash_set.is_empty t.wspill

  let rec main t ~round ~max_rounds =
    let open C.Syntax in
    let* () = C.when_ (round > max_rounds) @@ fun () ->
      C.failf "In Regalloc.main: maximum rounds reached (%d) with no \
               convergence on spilling" max_rounds () in
    (* Build the interference graph. *)
    let live = Live.compute ~keep:t.keep t.fn in
    build t live;
    (* Process the worklists. *)
    while not @@ should_stop t do
      if not @@ Hash_set.is_empty t.wsimplify then
        simplify t
      else if not @@ Lset.is_empty t.wmoves then
        coalesce t
      else if not @@ Hash_set.is_empty t.wfreeze then
        freeze t
      else if not @@ Hash_set.is_empty t.wspill then
        select_spill t
    done;
    (* Assign colors or spill. *)
    assign_colors t;
    (* Rewrite according to the spilled nodes. *)
    C.unless (Hash_set.is_empty t.spilled) @@ fun () ->
    let* () = rewrite_program t in
    main t ~round:(round + 1) ~max_rounds

  (* Initial set of stack slots. These should be excluded from consideration
     in the interference graph. *)
  let init_slots t =
    Func.slots t.fn |> Seq.iter ~f:(fun s ->
        Hash_set.add t.slots @@ Rv.var `gpr @@ Virtual.Slot.var s)

  (* initial: temporary registers, not preassigned a color and not yet
     processed by the algorithm. *)
  let init_initial t =
    let add_initial rv =
      if Rv.is_var rv
      && not (Hash_set.mem t.colored rv)
      && not (Hash_set.mem t.slots rv)
      then Hash_set.add t.initial rv in
    Func.blks t.fn |> Seq.iter ~f:(fun b ->
        Blk.insns b |> Seq.iter ~f:(fun i ->
            let insn = Insn.insn i in
            let use = M.Insn.reads insn in
            let def = M.Insn.writes insn in
            Set.iter use ~f:add_initial;
            Set.iter def ~f:add_initial))

  let apply_alloc t =
    let subst n = match Hashtbl.find t.colors n with
      | None -> assert (Rv.is_reg n || Hash_set.mem t.slots n); n
      | Some c -> Rv.reg @@ match classof n with
        | `gpr -> allocatable.(c)
        | `fp -> allocatable_fp.(c) in
    Func.blks t.fn |> Seq.map ~f:(fun b ->
        Blk.insns b |> Seq.map ~f:(fun i ->
            Insn.with_insn i @@ M.Regalloc.substitute (Insn.insn i) subst) |>
        Seq.to_list |> Blk.with_insns b) |>
    Seq.to_list |> Func.with_blks t.fn

  let run ?(max_rounds = 40) fn =
    let open C.Syntax in
    let t = create fn in
    init_slots t;
    init_initial t;
    let+ () = main t ~round:1 ~max_rounds in
    apply_alloc t
end
