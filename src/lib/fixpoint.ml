open Core
open Regular.Std

module Ltree = Label.Tree

module Solution = struct
  type 'd t = {
    map : 'd Ltree.t;
    def : 'd;
  }

  let create map def = {map; def}
  let get t l = Ltree.find t.map l |> Option.value ~default:t.def
  let default t = t.def
end

let (.![]) v i = Vec.unsafe_get v i
let (.![]<-) v i x = Vec.unsafe_set v i x

(* Compute the SCCs of the graph, which should give us a
   topological ordering perform the iteration by. *)
let components ~adj ~start ~n g =
  let rnodes = Label.Table.create ~size:n () in
  let nodes = Vec.create ~capacity:n () in
  let low = Vec.create ~capacity:n () in
  let onstk = ref Bitset.empty in
  let stk = Vec.create ~capacity:n () in
  let sccs = Vec.create ~capacity:16 () in
  let work = Vec.create ~capacity:16 () in
  let counter = ref 0 in
  (* Visiting a node for the first time *)
  let visit l =
    let d = !counter in
    incr counter;
    onstk := Bitset.set !onstk d;
    Hashtbl.set rnodes ~key:l ~data:d;
    Vec.push nodes l;
    Vec.push low d;
    Vec.push stk d;
    Vec.push work (l, ref (adj l g), d) in
  (* Construct the component *)
  let construct d =
    assert (not @@ Vec.is_empty stk);
    let scc = ref Bitset.empty in
    let go = ref true in
    while !go do
      let m = Vec.pop_exn stk in
      onstk := Bitset.clear !onstk m;
      scc := Bitset.set !scc m;
      if m = d then go := false
    done;
    Vec.push sccs !scc in
  (* Perform our DFS. *)
  visit start;
  while not (Vec.is_empty work) do
    let _, rem, d = Vec.back_exn work in
    match Seq.next !rem with
    | None ->
      ignore (Vec.pop_exn work);
      Vec.back work |> Option.iter ~f:(fun (_, _, p) ->
          let ld = low.![d] and lp = low.![p] in
          if ld < lp then low.![p] <- ld);
      if low.![d] = d then construct d
    | Some (s, rest) ->
      rem := rest;
      match Hashtbl.find rnodes s with
      | None -> visit s
      | Some s when Bitset.mem !onstk s ->
        if s < low.![d] then low.![d] <- s
      | Some _ -> ()
  done;
  Vec.rev_inplace sccs;
  nodes, rnodes, sccs

let run (type g) (module G : Label.Graph_s with type t = g)
    ?(rev = false) ?step
    ~start ~(init : _ Solution.t) ~equal ~merge ~f g =
  if not (G.Node.mem start g) then
    invalid_argf "Fixpoint.run: start node %a is not in the graph"
      Label.pps start ();
  let adj = if rev then G.Node.preds else G.Node.succs in
  let nodes, rnodes, sccs =
    components ~adj ~start ~n:(G.number_of_nodes g) g in
  let len = Vec.length nodes in
  let succs = Array.init len ~f:(fun i ->
      adj nodes.![i] g |>
      Seq.filter_map ~f:(Hashtbl.find rnodes) |>
      Seq.to_list) in
  (* Working approximation and per-node visit counts. *)
  let approx = Array.create ~len init.def in
  Ltree.iter init.map ~f:(fun ~key ~data ->
      match Hashtbl.find rnodes key with
      | Some i -> approx.(i) <- data
      | None -> ());
  let visits = Array.create ~len 0 in
  (* Two-level iteration: outer pass over SCCs in topological
     order, inner worklist within each SCC until convergence. *)
  Vec.iter sccs ~f:(fun scc ->
      let worklist = ref scc in
      while not (Bitset.is_empty !worklist) do
        let node, rest = Bitset.pop_min_elt_exn !worklist in
        worklist := rest;
        let out = f nodes.![node] approx.(node) in
        List.iter succs.(node) ~f:(fun s ->
            let prev = approx.(s) in
            let next = merge out prev in
            let next = match step with
              | None -> next
              | Some step ->
                visits.(s) <- visits.(s) + 1;
                step visits.(s) nodes.![s] prev next in
            if not (equal prev next) then
              let () = approx.(s) <- next in
              if Bitset.mem scc s then
                worklist := Bitset.set !worklist s)
      done);
  (* Reconstruct solution, omitting default-valued entries. *)
  let map = Array.foldi approx ~init:Ltree.empty ~f:(fun i acc v ->
      if equal v init.def then acc
      else Ltree.set acc ~key:nodes.![i] ~data:v) in
  {init with map}
