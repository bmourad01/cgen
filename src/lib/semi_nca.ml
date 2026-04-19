open Core
open Regular.Std
open Graphlib.Std

module Lset = Label.Tree_set
module LT = Label.Dense_table

type tree = {
  rev      : bool;
  root     : Label.t;
  parent   : Label.t LT.t;
  children : Label.t list LT.t Lazy.t;
  depth    : int LT.t Lazy.t;
  rpo      : int LT.t Lazy.t;
}

module Tree = struct
  type t = tree

  exception Not_found

  let is_reversed t = t.rev
  let root t = t.root
  let parent t n = LT.find t.parent n
  let depth t n = LT.find (Lazy.force t.depth) n
  let rpo t n = LT.find (Lazy.force t.rpo) n

  let children t n = match LT.find (Lazy.force t.children) n with
    | Some cs -> Seq.of_list cs
    | None -> Seq.empty

  let mem t n = Label.(n = t.root) || LT.mem t.parent n

  let parent_exn t n = match parent t n with
    | None -> raise Not_found
    | Some p -> p

  let depth_exn t n = match depth t n with
    | None -> raise Not_found
    | Some d -> d

  let rpo_exn t n = match rpo t n with
    | None -> raise Not_found
    | Some o -> o

  let rec is_descendant_of t ~parent n = match LT.find t.parent n with
    | Some p -> Label.(p = parent) || is_descendant_of t ~parent p
    | None -> false

  let dominates t a b = Label.(a = b) || is_descendant_of t ~parent:a b

  let descendants t n =
    let open Seq.Generator in
    let rec gen u =
      yield u >>= fun () ->
      children t u |> Seq.fold ~init:(return ())
        ~f:(fun acc c -> acc >>= fun () -> gen c) in
    run @@ gen n

  let postorder t =
    let open Seq.Generator in
    let rec gen u =
      let rec walk s = match Seq.next s with
        | Some (c, s) -> gen c >>= fun () -> walk s
        | None -> yield u in
      walk @@ children t u in
    run @@ gen t.root

  let preorder t = descendants t t.root

  let ancestors t n =
    let open Seq.Generator in
    let rec walk n = match LT.find t.parent n with
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
    while Label.(!ra <> !rb) do
      ra := parent_exn t !ra;
      rb := parent_exn t !rb;
    done;
    !ra

  let lca t a b = try Some (lca_exn t a b) with
    | Not_found -> None
end

type frontier = Lset.t LT.t

module Frontier = struct
  type t = frontier

  let get t n = match LT.find t n with
    | Some s -> s
    | None -> Lset.empty

  let mem t a b = match LT.find t a with
    | Some s -> Lset.mem s b
    | None -> false
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
  type node = {
    mutable ans  : int;
    mutable sdom : int;
    mutable best : int;
    mutable idom : int;
    self         : Label.t;
  }

  let create_node p n u = {
    ans = p;
    sdom = n;
    best = n;
    idom = p;
    self = u;
  }

  let ( .!() ) t i = Vec.unsafe_get t i

  type frame =
    | Enter of Label.t * int
    | Exit of Label.t

  (* Initialize the DFS spanning tree. *)
  let dfs g nums postord preord entry dir =
    let q = Stack.singleton @@ Enter (entry, 0) in
    Stack.until_empty q @@ function
    | Exit u -> Vec.push postord u
    | Enter (u, _) when LT.mem nums u -> ()
    | Enter (u, p) ->
      Stack.push q @@ Exit u;
      let n = Vec.length preord in
      LT.set nums ~key:u ~data:n;
      Vec.push preord @@ create_node p n u;
      (* Explore the children according to the ordering
         prescribed by `g`. *)
      dir u g |> Seq.filter ~f:(fun v ->
          not @@ LT.mem nums v) |>
      Seq.to_list_rev |> List.iter ~f:(fun v ->
          Stack.push q @@ Enter (v, n))

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
        Seq.filter_map ~f:(LT.find nums) |>
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
      LT.set idom ~key:vn.self ~data:preord.!(vn.idom).self
    done
end

let compute
    (type g)
    (module G : Label.Graph_s with type t = g) ?(rev = false) g entry =
  let dfs_dir = if rev then G.Node.preds else G.Node.succs in
  let sdom_dir = if rev then G.Node.succs else G.Node.preds in
  let capacity = G.number_of_nodes g in
  (* Map nodes to preorder numbers *)
  let nums = LT.create ~capacity () in
  (* Preorder spanning tree *)
  let postord = Vec.create ~capacity () in
  let preord = Vec.create ~capacity () in
  Impl.dfs g nums postord preord entry dfs_dir;
  (* Ancestor path. *)
  let path = Stack.create () in
  Impl.semi g path nums preord sdom_dir;
  (* Immediate dominators *)
  let parent = LT.create ~capacity () in
  Impl.idom parent preord;
  (* Reverse postorder numbering *)
  let rpo = lazy begin
    let t = LT.create ~capacity () in
    let n = Vec.length postord in
    Vec.iteri postord ~f:(fun i key ->
        LT.set t ~key ~data:(n - 1 - i));
    t end in
  (* Children of each node, sorted by RPO. *)
  let children = lazy begin
    let t = LT.create ~capacity () in
    G.nodes g |> Seq.iter ~f:(fun u ->
        LT.find parent u |> Option.iter ~f:(fun v ->
            LT.add_multi t ~key:v ~data:u));
    let rpo = Lazy.force rpo in
    LT.map_inplace t ~f:(fun cs ->
        List.dedup_and_sort cs ~compare:(fun a b ->
            let na = LT.find_exn rpo a in
            let nb = LT.find_exn rpo b in
            Int.compare na nb));
    t end in
  let depth = lazy begin
    let t = LT.create ~capacity () in
    let children = Lazy.force children in
    let q = Stack.singleton (entry, 0) in
    Stack.until_empty q (fun (n, d) ->
        LT.set t ~key:n ~data:d;
        LT.find children n |> Option.iter ~f:(fun cs ->
            List.iter cs ~f:(fun c -> Stack.push q (c, d + 1))));
    t end in
  {rev; root = entry; parent; children; depth; rpo}

(* Based on the paper "Efficiently Computing Static Single Assignment
   Form and the Control Dependence Graph" by Cytron et al. *)
let frontier
    (type g)
    (module G : Label.Graph_s with type t = g) g tree =
  let t = LT.create ~capacity:(G.number_of_nodes g) () in
  let add u v = match LT.find tree.parent v with
    | Some p when Label.(p <> u) ->
      LT.update t u ~f:(function
          | None -> Lset.singleton v
          | Some s -> Lset.add s v)
    | _ -> () in
  (* Compute DF_{local}. *)
  let dir = if tree.rev
    then fun e -> G.Edge.(dst e, src e)
    else fun e -> G.Edge.(src e, dst e) in
  G.edges g |> Seq.map ~f:dir |> Seq.iter ~f:(Tuple2.uncurry add);
  (* Compute DF, in a bottom-up traversal of the tree. *)
  Tree.postorder tree |> Seq.iter ~f:(fun u ->
      Tree.children tree u |>
      Seq.filter_map ~f:(LT.find t) |>
      Seq.iter ~f:(fun s -> Lset.iter s ~f:(add u)));
  t
