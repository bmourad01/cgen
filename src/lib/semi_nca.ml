open Core
open Regular.Std
open Graphlib.Std

type 'a tree = {
  rev      : bool;
  root     : 'a;
  equal    : 'a -> 'a -> bool;
  parent   : 'a -> 'a option;
  children : 'a -> 'a seq;
  depth    : 'a -> int option;
}

let preorder ~children n =
  let open Seq.Generator in
  let rec gen u =
    yield u >>= fun () ->
    children u |> Seq.fold ~init:(return ())
      ~f:(fun acc c ->  acc >>= fun () -> gen c) in
  run @@ gen n

module Tree = struct
  type 'a t = 'a tree

  exception Not_found

  let root t = t.root
  let parent t n = t.parent n
  let children t n = t.children n
  let depth t n = t.depth n
  let descendants t n = preorder ~children:t.children n
  let mem t n = t.equal n t.root || Option.is_some (t.parent n)

  let parent_exn t n = match t.parent n with
    | None -> raise Not_found
    | Some p -> p

  let depth_exn t n = match t.depth n with
    | None -> raise Not_found
    | Some d -> d

  let rec is_descendant_of t ~parent n = match t.parent n with
    | Some p -> t.equal p parent || is_descendant_of t ~parent p
    | None -> false

  let postorder t =
    let open Seq.Generator in
    let rec gen u =
      let rec walk s = match Seq.next s with
        | Some (c, s) -> gen c >>= fun () -> walk s
        | None -> yield u in
      walk @@ t.children u in
    run @@ gen t.root

  let preorder t = descendants t t.root

  let ancestors t n =
    let open Seq.Generator in
    let rec walk n = match t.parent n with
      | None -> return ()
      | Some p -> yield p >>= fun () -> walk p in
    run @@ walk n

  let lca_exn t a b =
    let ra = ref a
    and rb = ref b
    and da = ref (depth_exn t a)
    and db = ref (depth_exn t b) in
    (* While `a` is deeper than `b`, go up the tree. *)
    while !da > !db do
      ra := parent_exn t !ra;
      decr da;
    done;
    (* While `b` is deeper than `a`, go up the tree. *)
    while !db > !da do
      rb := parent_exn t !rb;
      decr db;
    done;
    (* Find the common ancestor. *)
    while not (t.equal !ra !rb) do
      ra := parent_exn t !ra;
      rb := parent_exn t !rb;
    done;
    !ra

  let lca t a b = try Some (lca_exn t a b) with
    | Not_found -> None
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

  let ( .!() ) t i = Vec.unsafe_get t i

  (* Initialize the DFS spanning tree. *)
  let dfs g nums preord entry dir =
    let q = Stack.singleton (entry, 0) in
    let not_visited n = not @@ Hashtbl.mem nums n in
    Stack.until_empty q @@ fun (u, p) -> if not_visited u then
      let n = Vec.length preord in
      Hashtbl.set nums ~key:u ~data:n;
      Vec.push preord @@ create_node p n u;
      dir u g |> Seq.iter ~f:(fun v -> Stack.push q (v, n))

  (* Compute the path containing v's ancestors. *)
  let rec ancestor_path ~stop path preord v =
    Stack.push path v;
    let v' = preord.!(v).ans in
    let v'' = preord.!(v').ans in
    if v'' < stop then v', v''
    else ancestor_path ~stop path preord v'

  (* Path compression. *)
  let compress ~stop path preord v =
    let init, root = ancestor_path ~stop path preord v in
    (* Walk the stack back down to v while performing path compression. *)
    let p = ref init in
    Stack.until_empty path @@ fun v ->
    let pn = preord.!(!p) and vn = preord.!(v) in
    if pn.best < vn.best then vn.best <- pn.best;
    vn.ans <- root;
    p := v

  (* Compute the ancestor of v with the smallest semidominator
     on the path to the root. *)
  let eval ~stop path preord v =
    let vn = preord.!(v) in
    if vn.ans >= stop then compress ~stop path preord v;
    vn.best

  (* Compute the semidominators *)
  let semi g path nums preord dir =
    for v = Vec.length preord - 1 downto 1 do
      let vn = preord.!(v) in
      let s =
        dir vn.self g |>
        Seq.filter_map ~f:(Hashtbl.find nums) |>
        Seq.map ~f:(eval ~stop:(v + 1) path preord) |>
        Seq.fold ~init:vn.ans ~f:min in
      vn.best <- s;
      vn.sdom <- s;
    done

  (* Compute the immediate dominators *)
  let idom idom preord =
    for v = 1 to Vec.length preord - 1 do
      let vn = preord.!(v) in
      while vn.idom > vn.sdom do
        vn.idom <- preord.!(vn.idom).idom
      done;
      Hashtbl.set idom ~key:vn.self ~data:preord.!(vn.idom).self
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
  (* Map nodes to preorder numbers *)
  let nums = G.Node.Table.create () in
  (* Preorder spanning tree *)
  let preord = Vec.create () in
  Impl.dfs g nums preord entry dfs_dir;
  (* Ancestor path. *)
  let path = Stack.create () in
  Impl.semi g path nums preord sdom_dir;
  (* Immediate dominators *)
  let idom = G.Node.Table.create () in
  Impl.idom idom preord;
  (* The resulting tree methods *)
  let parent u = Hashtbl.find idom u in
  let children =
    let t = lazy begin
      let t = G.Node.Table.create () in
      G.nodes g |> Seq.iter ~f:(fun u ->
          parent u |> Option.iter ~f:(fun v ->
              Hashtbl.update t v ~f:(function
                  | None -> G.Node.Set.singleton u
                  | Some s -> Set.add s u)));
      t end in
    fun n -> match Hashtbl.find (Lazy.force t) n with
      | Some s -> Set.to_sequence s
      | None -> Seq.empty in
  let depth =
    let t = lazy begin
      let t = G.Node.Table.create () in
      let q = Stack.singleton (entry, 0) in
      Stack.until_empty q (fun (n, d) ->
          Hashtbl.set t ~key:n ~data:d;
          children n |> Seq.iter ~f:(fun c ->
              Stack.push q (c, d + 1)));
      t end in
    fun n -> Hashtbl.find (Lazy.force t) n in
  {rev; root = entry; equal = G.Node.equal; parent; children; depth}

(* Based on the paper "Efficiently Computing Static Single Assignment
   Form and the Control Dependence Graph" by Cytron et al. *)
let frontier
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) g tree =
  let t = G.Node.Table.create () in
  let enum a = match Hashtbl.find t a with
    | Some s -> Set.to_sequence s
    | None -> Seq.empty in
  let mem a b = match Hashtbl.find t a with
    | Some s -> Set.mem s b
    | None -> false in
  let add u v = match tree.parent v with
    | Some p when G.Node.(p <> u) ->
      Hashtbl.update t u ~f:(function
          | None -> G.Node.Set.singleton v
          | Some s -> Set.add s v)
    | _ -> () in
  (* Compute DF_{local}. *)
  let dir = if tree.rev
    then fun e -> G.Edge.(dst e, src e)
    else fun e -> G.Edge.(src e, dst e) in
  G.edges g |> Seq.map ~f:dir |> Seq.iter ~f:(Tuple2.uncurry add);
  (* Compute DF, in a bottom-up traversal of the tree. *)
  Tree.postorder tree |> Seq.iter ~f:(fun u ->
      tree.children u |> Seq.bind ~f:enum |>
      Seq.iter ~f:(add u));
  {enum; mem}
