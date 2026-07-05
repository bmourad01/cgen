open Core
module Regular = Cgen_utils.Regular
open Cgen_containers

module T = struct
  type t = int [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

type label = t [@@deriving bin_io, compare, equal, sexp]

let of_int_unsafe l = l

(* NOTE: do not change these constants, unless you want to redo all of the
   file tests. *)
let pseudoentry = 0
let pseudoexit = 1

let is_pseudo l = l = pseudoentry || l = pseudoexit

let pp ppf = function
  | l when l = pseudoentry -> Format.fprintf ppf "@pseudoentry"
  | l when l = pseudoexit -> Format.fprintf ppf "@pseudoexit"
  | l -> Format.fprintf ppf "@%d" l

module R = Regular.Make(struct
    include T
    let pp = pp
  end)

include R

module Patricia_key = struct
  include Int
  let size = 63
  let equal : t -> t -> bool = phys_equal
end

module Dense_key = struct
  type t = label
  let empty_sentinel = -1
  let to_int l = l
  let pp = pp
  let equal : t -> t -> bool = phys_equal
end

module Tree = Patricia_tree.Make(Patricia_key)
module Tree_set = Patricia_tree.Make_set(Patricia_key)
module Dense_table = Dense.Make_map(Dense_key)
module Dense_set = Dense.Make_set(Dense_key)

module Graph = struct
  type edge = {
    src : label;
    dst : label;
  } [@@deriving fields]

  type arrows = Tree_set.t

  type node_info = {
    inc : arrows;
    out : arrows;
  } [@@deriving fields]

  type graph = node_info Tree.t

  let empty_node = {
    inc = Tree_set.empty;
    out = Tree_set.empty;
  } [@@deriving fields]

  module Node = struct
    let mem n g = Tree.mem g n

    let adj dir n g = Tree.find g n |> function
      | None -> Sequence.empty
      | Some ns -> Tree_set.to_sequence (dir ns)

    let succs n = adj out n
    let preds n = adj inc n

    let edges dir reorder n g = Tree.find g n |> function
      | None -> Sequence.empty
      | Some ns ->
        Tree_set.to_sequence (dir ns) |>
        Sequence.map ~f:(fun m ->
            let src, dst = reorder n m in
            {src; dst})

    let inputs n = edges inc (fun dst src -> src, dst) n
    let outputs n = edges out (fun src dst -> src, dst) n

    let insert n g = Tree.change g n ~f:(function
        | None -> Some empty_node
        | other -> other)

    let remove_arrow field info arrs n =
      let arrs = Tree_set.remove arrs n in
      Some (Field.fset field info arrs)

    let update_arrows update field neibs n g : graph =
      Tree_set.fold neibs ~init:g ~f:(fun g m ->
          Tree.change g m ~f:(function
              | None -> None
              | Some info ->
                update field info (Field.get field info) n))

    let remove_arrows = update_arrows remove_arrow

    let remove n g = match Tree.find g n with
      | None -> g
      | Some {inc; out} ->
        Tree.remove g n |>
        remove_arrows Fields_of_node_info.out inc n |>
        remove_arrows Fields_of_node_info.inc out n

    let edge src (dst : label) g = match Tree.find g src with
      | Some a when Tree_set.mem a.out dst -> Some {src; dst}
      | Some _ | None -> None

    let has_edge src dst g = Option.is_some @@ edge src dst g

    let degree select n g = match Tree.find g n with
      | None -> 0
      | Some s -> Tree_set.length (select s)

    let degree ?dir n g = match dir with
      | None -> degree inc n g + degree out n g
      | Some `In -> degree inc n g
      | Some `Out -> degree out n g

    include T
    include R
  end

  module Edge = struct
    let create src dst = {src; dst}
    let src e = e.src
    let dst e = e.dst

    let mem e g = match Tree.find g e.src with
      | None -> false
      | Some a -> Tree_set.mem a.out e.dst

    let upsert_arrow src dst field e g =
      Tree.change g (src e) ~f:(function
          | None ->
            Some (Field.fset field empty_node (Tree_set.singleton (dst e)))
          | Some ns ->
            let map = Field.get field ns in
            Some (Field.fset field ns (Tree_set.add map (dst e))))

    let remove_arrow field arr src g = Tree.change g src ~f:(function
        | None -> None
        | Some ns ->
          let set = Field.get field ns in
          Some (Field.fset field ns (Tree_set.remove set arr)))

    let upsert e g =
      upsert_arrow src dst Fields_of_node_info.out e g |>
      upsert_arrow dst src Fields_of_node_info.inc e

    let insert e g = if mem e g then g else upsert e g

    let remove e g : graph =
      remove_arrow Fields_of_node_info.out e.dst e.src g |>
      remove_arrow Fields_of_node_info.inc e.src e.dst
  end

  type t = graph
  type node = Node.t

  let empty = Tree.empty

  let nodes g = Tree.to_sequence g |> Sequence.map ~f:fst
  let edges g = nodes g |> Sequence.concat_map ~f:(fun src -> Node.outputs src g)
  let number_of_nodes g = Tree.length g

  let number_of_edges g =
    Tree.fold g ~init:0 ~f:(fun ~key:_ ~data:{out; _} sum ->
        sum + Tree_set.length out)
end

module Pseudo = struct
  let connect_with_entry n =
    if n = pseudoentry then Fn.id
    else Graph.Edge.(insert (create pseudoentry n))

  let connect_with_exit n =
    if n = pseudoexit then Fn.id
    else Graph.Edge.(insert (create n pseudoexit))

  let if_unreachable ~from connect g n =
    match Graph.Node.degree ~dir:from n g with
    | 0 -> connect n
    | _ -> Fn.id

  let connect_unreachable g n =
    if_unreachable ~from:`Out connect_with_exit  g n @@
    if_unreachable ~from:`In  connect_with_entry g n @@
    g

  let add g =
    let[@inline] propagate g v q =
      Stack.until_empty q @@ fun n ->
      if Dense_set.strict_add v n then
        Graph.Node.preds n g |> Sequence.iter ~f:(Stack.push q) in
    let g0 = Graph.nodes g |> Sequence.fold ~init:g ~f:connect_unreachable in
    let q = Stack.create () in
    let v = Dense_set.create () in
    Dense_set.add v pseudoexit;
    Graph.Node.preds pseudoexit g0 |> Sequence.iter ~f:(Stack.push q);
    propagate g0 v q;
    Graph.nodes g |> Sequence.fold ~init:g0 ~f:(fun g n ->
        if Dense_set.strict_add v n then
          let () = Graph.Node.preds n g |> Sequence.iter ~f:(Stack.push q) in
          propagate g0 v q;
          connect_with_exit n g
        else g)
end
