open Core
open Regular.Std
open Graphlib.Std

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

let run (type g) (module G : Label.Graph_s with type t = g)
    ?(start = Label.pseudoentry) ?(rev = false) ?step
    ~(init : _ Solution.t) ~equal ~merge ~f g =
  (* Assign RPO indices, reversed if backward analysis. *)
  let nodes =
    Graphlib.reverse_postorder_traverse (module G)
      ~rev ~start g |> Sequence.to_array in
  let n = Array.length nodes in
  let rnodes = Label.Table.create ~size:n () in
  Array.iteri nodes ~f:(fun data key ->
      Hashtbl.set rnodes ~key ~data);
  (* Pre-compute successor RPO-index lists. *)
  let adj = if rev then G.Node.preds else G.Node.succs in
  let succs = Array.map nodes ~f:(fun l ->
      adj l g |>
      Seq.filter_map ~f:(Hashtbl.find rnodes) |>
      Seq.to_list) in
  (* Working approximation and per-node visit counts. *)
  let approx = Array.create ~len:n init.def in
  Ltree.iter init.map ~f:(fun ~key ~data ->
      match Hashtbl.find rnodes key with
      | Some i -> approx.(i) <- data
      | None -> ());
  let visits = Array.create ~len:n 0 in
  (* Compute the topological ordering of SCCs. Each SCC
     is initially identified as its representative label. *)
  let comps = Graphlib.strong_components (module G) g in
  let scc_of l = match Partition.group comps l with
    | Some grp -> Group.top grp
    | None -> l in
  let scc_idx = Option_array.create ~len:n in
  let sccs = Vec.create ~capacity:n () in
  Array.iteri nodes ~f:(fun i l ->
      let j =
        scc_of l |>
        Hashtbl.find rnodes |>
        Option.value ~default:i in
      let k = match Option_array.get scc_idx j with
        | Some k -> k
        | None ->
          let k = Vec.length sccs in
          Option_array.set_some scc_idx j k;
          Vec.push sccs Bitset.empty;
          k in
      let s = Vec.get_exn sccs k in
      Vec.set_exn sccs k (Bitset.set s i));
  (* Two-level iteration: outer pass over SCCs in topological
     order, inner worklist within each SCC until convergence. *)
  Vec.iter sccs ~f:(fun scc ->
      let worklist = ref scc in
      while not (Bitset.is_empty !worklist) do
        let node, rest = Bitset.pop_min_elt_exn !worklist in
        worklist := rest;
        let out = f nodes.(node) approx.(node) in
        List.iter succs.(node) ~f:(fun s ->
            let prev = approx.(s) in
            let next = merge out prev in
            let next = match step with
              | None -> next
              | Some step ->
                visits.(s) <- visits.(s) + 1;
                step visits.(s) nodes.(s) prev next in
            if not (equal prev next) then
              let () = approx.(s) <- next in
              if Bitset.mem scc s then
                worklist := Bitset.set !worklist s)
      done);
  (* Reconstruct solution, omitting default-valued entries. *)
  let map = Array.foldi approx ~init:Ltree.empty ~f:(fun i acc v ->
      if equal v init.def then acc
      else Ltree.set acc ~key:nodes.(i) ~data:v) in
  {init with map}
