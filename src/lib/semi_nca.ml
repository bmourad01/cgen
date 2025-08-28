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

let idom
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?(rev = false) g entry =
  (* DFS preorder. *)
  let preord = Vec.create () in
  (* Immediate parent in the DFS tree. *)
  let parent = G.Node.Table.create () in
  (* Preorder numberings. *)
  let pre = G.Node.Table.create () in
  (* Union-find parent in the DFS tree. *)
  let ans = G.Node.Table.create () in
  (* Pending semidominated nodes. *)
  let chld = G.Node.Table.create () in
  (* Semidominator with the smallest DFS preorder number. *)
  let best = G.Node.Table.create () in
  (* Semidominators. *)
  let sdom = G.Node.Table.create () in
  (* Immediate dominators *)
  let idom = G.Node.Table.create () in
  let ( .![] ) t k = Hashtbl.find_exn t k in
  let ( .![]<- ) t k v = Hashtbl.set t ~key:k ~data:v in
  (* Perform path compression according to the ancestor table. *)
  let rec compress v =
    Hashtbl.find ans v |> Option.iter ~f:(fun a ->
        if Hashtbl.mem ans a then begin
          compress a;
          let ba = best.![a] in
          if pre.![ba] < pre.![best.![v]] then
            best.![v] <- ba;
          ans.![v] <- ans.![a]
        end) in
  (* Get the updated `best` link to `v` when performing path compression. *)
  let eval v = compress v; best.![v] in
  (* Pre-order traversal. *)
  let dir = if rev then G.Node.preds else G.Node.succs in
  let rec dfs u =
    best.![u] <- u;
    sdom.![u] <- u;
    pre.![u] <- Vec.length preord;
    Vec.push preord u;
    dir u g |> Seq.iter ~f:(fun v ->
        if not @@ Hashtbl.mem pre v then begin
          parent.![v] <- u;
          dfs v
        end) in
  dfs entry;
  (* Process in reverse preorder, skipping the entry node. *)
  let dir = if rev then G.Node.succs else G.Node.preds in
  for iv = Vec.length preord - 1 downto 1 do
    (* Find v's semidominator. *)
    let v = Vec.unsafe_get preord iv in
    dir v g |> Seq.iter ~f:(fun u ->
        let iu = pre.![u] in
        let s, is =
          if iu < iv then u, iu
          else
            let s = sdom.![eval u] in
            s, pre.![s] in
        let sv = sdom.![v] in
        if is < pre.![sv] then sdom.![v] <- s);
    (* Enqueue v to be processed in order to find its immediate
       dominator. *)
    Hashtbl.update chld sdom.![v] ~f:(function
        | None -> G.Node.Set.singleton v
        | Some s -> Set.add s v);
    let p = parent.![v] in
    (* v's initial ancestor is its DFS parent. *)
    ans.![v] <- p;
    (* Find the immediate dominators of the nodes semidominated
       by v's parent. *)
    Hashtbl.find chld p |>
    Option.value ~default:G.Node.Set.empty |>
    Set.iter ~f:(fun w ->
        let u = eval w in
        idom.![w] <- if pre.![sdom.![u]] < pre.![sdom.![w]] then u else p);
    Hashtbl.remove chld p;
  done;
  (* Fix up the immediate dominator table. *)
  for i = 1 to Vec.length preord - 1 do
    let v = Vec.unsafe_get preord i in
    let dv = idom.![v] in
    if G.Node.(dv <> sdom.![v]) then
      idom.![v] <- idom.![dv]
  done;
  Hashtbl.find idom

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
       and type node = n) ?(rev = false) g tree : n frontier =
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
