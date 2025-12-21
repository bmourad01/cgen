open Core
open Regular.Std
open Graphlib.Std

let ( .!() ) t i = Vec.unsafe_get t i

type 'a tree = {
  rev              : bool;
  root             : 'a;
  parent           : 'a -> 'a option;
  children         : 'a -> 'a seq;
  descendants      : 'a -> 'a seq;
  ancestors        : 'a -> 'a seq;
  is_descendant_of : parent:'a -> 'a -> bool;
}

module Tree = struct
  type 'a t = 'a tree

  let parent t = t.parent
  let children t = t.children
  let descendants t = t.descendants
  let ancestors t = t.ancestors
  let is_descendant_of t = t.is_descendant_of

  let postorder t =
    let open Seq.Generator in
    let rec gen u =
      let rec walk s = match Seq.next s with
        | Some (c, s) -> gen c >>= fun () -> walk s
        | None -> yield u in
      walk @@ t.children u in
    run @@ gen t.root

  let preorder t =
    let open Seq.Generator in
    let rec gen u =
      yield u >>= fun () ->
      t.children u |> Seq.fold ~init:(return ())
        ~f:(fun acc c ->  acc >>= fun () -> gen c) in
    run @@ gen t.root
end

type 'a frontier = {
  enum : 'a -> 'a seq;
  mem  : 'a -> 'a -> bool;
}

module Frontier = struct
  type 'a t = 'a frontier
  let enum t = t.enum
  let mem t = t.mem
end

(* Implementation of the SEMI-NCA algorithm from:
   "Linear-time algorithms for dominators and related problems"
   by L. Geordiadis (2005)

   This is a simplification of the Lengauer-Tarjan (LT) algorithm,
   removing a lot of the subtle data structure invariants while still
   maintaining a linear time complexity.

   This relies on the concept of a "semidominator" in order to find the
   immediate dominators of each node. A semidominator identifies the earliest
   point where dominance could start for a given node.

   The Cooper-Harvey-Kennedy algorithm is even simpler, but has a
   worst-case time time complexity of O(VE). This is the implementation
   used in [Graphlib].

   Another benefit of this algorithm is that it becomes easier to
   engineer an "incremental" version for when the graph is updated,
   removing the need to always rebuild the entire dominator tree.
*)
module Impl = struct
  (* DFS preorder node. All [int]s refer to nodes by DFS pre-order number.

     [ans]:  the union-find ancestor pointer; this is initially the parent
             node in the DFS tree
     [sdom]: the semidominator
     [best]: the node with the smallest semidominator seen so far along
             the path to the root
     [idom]: the immediate dominator
     [self]: the node itself
  *)
  type 'a node = {
    mutable ans  : int;
    mutable sdom : int;
    mutable best : int;
    mutable idom : int;
    self         : 'a;
  }

  let create_node p n u = {
    ans = p;
    sdom = n;
    best = n;
    idom = p;
    self = u;
  }

  (* Initialize the DFS spanning tree. *)
  let dfs g pre entry dir =
    let preord = Vec.create () in
    let q = Stack.singleton (entry, 0) in
    let not_visited n = not @@ Hashtbl.mem pre n in
    Stack.until_empty q (fun (u, p) ->
        if not_visited u then
          let n = Vec.length preord in
          Hashtbl.set pre ~key:u ~data:n;
          Vec.push preord @@ create_node p n u;
          dir u g |> Seq.filter ~f:not_visited |>
          Seq.iter ~f:(fun v -> Stack.push q (v, n)));
    preord

  (* Compute the path containing v's ancestors. *)
  let rec ancestor_path ~stop preord root acc =
    let acc = root :: acc in
    let root = preord.!(root).ans in
    let root' = preord.!(root).ans in
    if root' >= stop
    then ancestor_path ~stop preord root acc
    else acc, root, root'

  (* Path compression. *)
  let compress ~stop preord v =
    let stk, init, root = ancestor_path ~stop preord v [] in
    (* Walk the stack back down to v while performing path compression. *)
    ignore @@ List.fold stk ~init ~f:(fun p v ->
        let pn = preord.!(p) and vn = preord.!(v) in
        if pn.best < vn.best then vn.best <- pn.best;
        vn.ans <- root; v)

  (* Compute the ancestor of v with the smallest semidominator
     on the path to the root. *)
  let eval ~stop preord v =
    let vn = preord.!(v) in
    if vn.ans >= stop then compress ~stop preord v;
    vn.best

  (* Compute the semidominators *)
  let semi g pre preord dir =
    for v = Vec.length preord - 1 downto 1 do
      let vn = preord.!(v) in
      let s =
        dir vn.self g |>
        Seq.filter_map ~f:(Hashtbl.find pre) |>
        Seq.map ~f:(eval ~stop:(v + 1) preord) |>
        Seq.fold ~init:vn.ans ~f:min in
      vn.best <- s;
      vn.sdom <- s;
    done

  (* Compute the immediate dominators *)
  let idom t preord =
    for v = 1 to Vec.length preord - 1 do
      let vn = preord.!(v) in
      while vn.idom > vn.sdom do
        vn.idom <- preord.!(vn.idom).idom
      done;
      Hashtbl.set t ~key:vn.self ~data:preord.!(vn.idom).self
    done
end

let compute
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?(rev = false) g entry =
  (* The algorithm itself *)
  let dfs_dir = if rev then G.Node.preds else G.Node.succs in
  let sdom_dir = if rev then G.Node.succs else G.Node.preds in
  let pre = G.Node.Table.create () in
  let preord = Impl.dfs g pre entry dfs_dir in
  Impl.semi g pre preord sdom_dir;
  let t = G.Node.Table.create () in
  Impl.idom t preord;
  (* The resulting tree methods *)
  let parent u = Hashtbl.find t u in
  let children = lazy begin
    let t = G.Node.Table.create () in
    G.nodes g |> Seq.iter ~f:(fun u ->
        parent u |> Option.iter ~f:(fun v ->
            Hashtbl.update t v ~f:(function
                | None -> G.Node.Set.singleton u
                | Some s -> Set.add s u)));
    t end in
  let rec descendants acc = function
    | [] -> Set.to_sequence acc
    | x :: rest ->
      let acc, rest =
        match Hashtbl.find (Lazy.force children) x with
        | None -> acc, rest
        | Some s ->
          Set.union acc s,
          Set.fold s ~init:rest ~f:(Fn.flip List.cons) in
      descendants acc rest in
  let rec is_descendant_of ~parent n = match Hashtbl.find t n with
    | Some p -> G.Node.(parent = p) || is_descendant_of ~parent p
    | None -> false in
  let rec ancestors acc n = match parent n with
    | Some p -> ancestors (Set.add acc p) p
    | None -> Set.to_sequence acc in
  let children n = match Hashtbl.find (Lazy.force children) n with
    | Some s -> Set.to_sequence s
    | None -> Seq.empty in
  let ancestors n = ancestors G.Node.Set.empty n in
  let descendants n = descendants G.Node.Set.empty [n] in {
    rev;
    root = entry;
    parent;
    children;
    descendants;
    ancestors;
    is_descendant_of
  }

let frontier
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) g tree =
  let t = G.Node.Table.create () in
  (* Based on the paper "Efficiently Computing Static Single Assignment
     Form and the Control Dependence Graph" by Cytron et al. *)
  let update u v = match tree.parent v with
    | Some p when G.Node.(p <> u) ->
      Hashtbl.update t u ~f:(function
          | None -> G.Node.Set.singleton v
          | Some s -> Set.add s v)
    | Some _ | None -> () in
  (* Compute DF_{local}. *)
  let dir = if tree.rev
    then fun e -> G.Edge.(dst e, src e)
    else fun e -> G.Edge.(src e, dst e) in
  G.edges g |> Seq.map ~f:dir |>
  Seq.iter ~f:(fun (u, v) -> update u v);
  (* Compute DF, in a bottom-up traversal of the tree. *)
  Tree.postorder tree |> Seq.iter ~f:(fun u ->
      tree.children u |> Seq.iter ~f:(fun c ->
          Hashtbl.find t c |> Option.iter ~f:(fun ys ->
              Set.iter ys ~f:(update u))));
  let enum a = match Hashtbl.find t a with
    | Some s -> Set.to_sequence s
    | None -> Seq.empty in
  let mem a b = match Hashtbl.find t a with
    | Some s -> Set.mem s b 
    | None -> false in
  {enum; mem}
