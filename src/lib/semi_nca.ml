open Core
open Regular.Std
open Graphlib.Std

type 'a tree = {
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

module Iset = Patricia_tree.Make_set(struct
    include Int
    let size = Sys.int_size_in_bits
  end)

(* DFS preorder node. *)
type 'a node = {
  parent       : int Uopt.t;
  mutable ans  : int Uopt.t;
  mutable sdom : int;
  mutable best : int;
  mutable idom : int Uopt.t;
  mutable chld : Iset.t;
  self         : 'a;
}

let idom
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?(rev = false) g entry =
  (* DFS preorder. *)
  let preord = Vec.create () in
  (* Preorder numberings. *)
  let pre = G.Node.Table.create () in
  let ( .!() ) t i = Vec.unsafe_get t i in
  let ( .![] ) t k = Hashtbl.find_exn t k in
  let ( .![]<- ) t k v = Hashtbl.set t ~key:k ~data:v in
  (* Perform path compression according to the ancestor table. *)
  let rec compress v =
    let vn = preord.!(v) in
    let a = Uopt.value_exn vn.ans in
    let an = preord.!(a) in
    if Uopt.is_some an.ans then begin
      compress a;
      if an.best < vn.best then
        vn.best <- an.best;
      vn.ans <- an.ans
    end in
  (* Get the updated `best` link to `v` when performing path compression. *)
  let eval v =
    let vn = preord.!(v) in
    if Uopt.is_some vn.ans then compress v;
    vn.best in
  (* Pre-order traversal. *)
  let dir = if rev then G.Node.preds else G.Node.succs in
  let rec dfs ?p u =
    let n = Vec.length preord in
    pre.![u] <- n;
    let parent = match p with
      | None -> Uopt.none
      | Some p -> Uopt.some pre.![p] in
    Vec.push preord {
      parent;
      ans = Uopt.none;
      sdom = n;
      best = n;
      idom = Uopt.none;
      chld = Iset.empty;
      self = u;
    };
    dir u g |>
    Seq.filter ~f:(Fn.non @@ Hashtbl.mem pre) |>
    Seq.iter ~f:(dfs ~p:u) in
  dfs entry;
  (* Process in reverse preorder, skipping the entry node. *)
  let dir = if rev then G.Node.succs else G.Node.preds in
  for iv = Vec.length preord - 1 downto 1 do
    (* Find v's semidominator. *)
    let vn = Vec.unsafe_get preord iv in
    dir vn.self g |> Seq.iter ~f:(fun u ->
        let iu = pre.![u] in
        let s = if iu < iv then iu
          else preord.!(eval iu).sdom in
        if s < vn.sdom then vn.sdom <- s);
    (* Enqueue v to be processed in order to find its immediate
       dominator. *)
    let svn = preord.!(vn.sdom) in
    svn.chld <- Iset.add svn.chld iv;
    (* v's initial ancestor is its DFS parent. *)
    let p = Uopt.value_exn vn.parent in
    vn.ans <- Uopt.some p;
    (* Find the immediate dominators of the nodes semidominated
       by v's parent. *)
    let pn = preord.!(p) in
    Iset.iter pn.chld ~f:(fun w ->
        let u = eval w in
        let wn = preord.!(w) in
        let un = preord.!(u) in
        wn.idom <- Uopt.some @@ if un.sdom < wn.sdom then u else p);
    pn.chld <- Iset.empty;
  done;
  (* Fix up the immediate dominator table. *)
  for v = 1 to Vec.length preord - 1 do
    let vn = preord.!(v) in
    let dv = Uopt.value_exn vn.idom in
    if dv <> vn.sdom then
      vn.idom <- preord.!(dv).idom
  done;
  fun u ->
    Hashtbl.find pre u |>
    Option.bind ~f:(fun iu ->
        Uopt.to_option preord.!(iu).idom) |>
    Option.map ~f:(fun id -> preord.!(id).self)

let compute
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?(rev = false) g entry =
  let parent = idom (module G) ~rev g entry in
  let init = G.nodes g |> Seq.fold ~init:G.Node.Map.empty ~f:(fun t n ->
      Map.set t ~key:n ~data:[]) in
  let children = G.nodes g |> Seq.fold ~init ~f:(fun tree n ->
      match parent n with
      | Some p -> Map.add_multi tree ~key:p ~data:n
      | None -> tree) |> Map.map ~f:G.Node.Set.of_list in
  let rec descendants n = match Map.find children n with
    | None -> G.Node.Set.empty
    | Some s ->
      Set.fold s ~init:s ~f:(fun s c ->
          Set.union s @@ descendants c) in
  let rec is_descendant_of ~parent n = match Map.find children parent with
    | None -> false
    | Some s -> Set.mem s n || Set.exists s ~f:(fun c ->
        is_descendant_of ~parent:c n) in
  let rec ancestors n = match parent n with
    | None -> G.Node.Set.empty
    | Some p -> Set.add (ancestors p) p in
  let children n = match Map.find children n with
    | None -> Seq.empty
    | Some s -> Set.to_sequence s in
  let descendants n = Set.to_sequence @@ descendants n in
  let ancestors n = Set.to_sequence @@ ancestors n in
  {parent; children; descendants; ancestors; is_descendant_of}

let frontier
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?(rev = false) g (tree : n tree) : n frontier =
  let adj = if rev then G.Node.succs else G.Node.preds in
  let idom = tree.parent in
  let rec walk top dfs r =
    if Option.equal G.Node.equal (Some r) top then dfs
    else match idom r with
      | None -> Set.add dfs r
      | Some p -> walk top (Set.add dfs r) p in
  let m =
    G.nodes g |> Seq.fold ~init:G.Node.Map.empty ~f:(fun dfs n ->
        let adj = adj n g in
        let dom = idom n in
        Seq.fold adj ~init:G.Node.Set.empty ~f:(walk dom) |>
        Set.fold ~init:dfs ~f:(fun dfs visited ->
            Map.update dfs visited ~f:(function
                | None -> G.Node.Set.singleton n
                | Some set -> Set.add set n))) in
  let enum a = match Map.find m a with
    | Some s -> Set.to_sequence s
    | None -> Seq.empty in
  let mem a b = match Map.find m a with
    | Some s -> Set.mem s b 
    | None -> false in
  {enum; mem}
