open Core
open Regular.Std
open Graphlib.Std

let ( .!() ) t i = Vec.unsafe_get t i

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

(* DFS preorder node. *)
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

let not_visited pre = Fn.non @@ Hashtbl.mem pre

(* Initialize the DFS spanning tree. *)
let dfs g pre entry dir =
  let preord = Vec.create () in
  let q = Stack.singleton (entry, 0) in
  Stack.until_empty q (fun (u, p) ->
      if not_visited pre u then
        let n = Vec.length preord in
        Hashtbl.set pre ~key:u ~data:n;
        Vec.push preord @@ create_node p n u;
        dir u g |> Seq.filter ~f:(not_visited pre) |>
        Seq.iter ~f:(fun v -> Stack.push q (v, n)));
  preord

(* Compute the path containing v's ancestors. *)
let rec ancestor_path ~stop preord root acc =
  let acc = root :: acc in
  let root = preord.!(root).ans in
  if preord.!(root).ans >= stop
  then ancestor_path ~stop preord root acc
  else acc, root

(* Path compression. *)
let compress ~stop preord v =
  let stk, init = ancestor_path ~stop preord v [] in
  let root = preord.!(init).ans in
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

let compute
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?(rev = false) g entry =
  (* The algorithm itself: *)
  let dfs_dir = if rev then G.Node.preds else G.Node.succs in
  let sdom_dir = if rev then G.Node.succs else G.Node.preds in
  let pre = G.Node.Table.create () in
  let preord = dfs g pre entry dfs_dir in
  semi g pre preord sdom_dir;
  let t = G.Node.Table.create () in
  idom t preord;
  (* The resulting tree methods: *)
  let parent u = Hashtbl.find t u in
  let children = G.Node.Table.create () in
  G.nodes g |> Seq.iter ~f:(fun u ->
      parent u |> Option.iter ~f:(fun v ->
          Hashtbl.update children v ~f:(function
              | None -> G.Node.Set.singleton u
              | Some s -> Set.add s u)));
  let rec descendants n acc = function
    | [] -> Set.to_sequence acc
    | x :: rest ->
      let acc, rest = match Hashtbl.find children x with
        | None -> acc, rest
        | Some s ->
          Set.union acc s,
          Set.fold s ~init:rest ~f:(Fn.flip List.cons) in
      descendants n acc rest in
  let rec is_descendant_of ~parent n = match Hashtbl.find t n with
    | Some p -> G.Node.(parent = p) || is_descendant_of ~parent p
    | None -> false in
  let rec ancestors acc n = match parent n with
    | Some p -> ancestors (Set.add acc p) p
    | None -> Set.to_sequence acc in
  let children n = match Hashtbl.find children n with
    | Some s -> Set.to_sequence s
    | None -> Seq.empty in
  let ancestors n = ancestors G.Node.Set.empty n in
  let descendants n = descendants n G.Node.Set.empty [n] in
  {parent; children; descendants; ancestors; is_descendant_of}

let frontier
    (type t n e)
    (module G : Graph
      with type t = t
       and type edge = e
       and type node = n) ?(rev = false) g tree =
  let dir = if rev then G.Node.succs else G.Node.preds in
  let t = G.Node.Table.create () in
  (* Figure 5 from the paper "A Simple, Fast Dominance Algorithm" *)
  let rec walk b b' runner =
    if G.Node.(runner <> b') then begin
      Hashtbl.update t runner ~f:(function
          | None -> G.Node.Set.singleton b
          | Some s -> Set.add s b);
      match tree.parent runner with
      | Some runner' -> walk b b' runner'
      | None -> ()
    end in
  G.nodes g |> Seq.iter ~f:(fun b ->
      tree.parent b |> Option.iter ~f:(fun b' ->
          match Seq.to_list @@ dir b g with
          | [] | [_] -> ()
          | xs -> List.iter xs ~f:(walk b b')));
  let enum a = match Hashtbl.find t a with
    | Some s -> Set.to_sequence s
    | None -> Seq.empty in
  let mem a b = match Hashtbl.find t a with
    | Some s -> Set.mem s b 
    | None -> false in
  {enum; mem}
