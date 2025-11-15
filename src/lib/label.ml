open Core
open Graphlib.Std
open Regular.Std

module T = struct
  type t = Int63.t [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

type label = t [@@deriving bin_io, compare, equal, sexp]

(* NOTE: do not change these constants, unless you want to redo all of the
   file tests. *)
let pseudoentry = Int63.zero
let pseudoexit = Int63.succ pseudoentry

let is_pseudo l = Int63.(l = pseudoentry || l = pseudoexit)

let pp ppf = function
  | l when Int63.(l = pseudoentry) -> Format.fprintf ppf "@pseudoentry"
  | l when Int63.(l = pseudoexit) -> Format.fprintf ppf "@pseudoexit"
  | l -> Format.fprintf ppf "@%a" Int63.pp l

module R = Regular.Make(struct
    include T
    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Label"
  end)

include R

module Tree = Patricia_tree.Make(struct
    include Int63
    let size = 63
  end)

module Tree_set = Patricia_tree.Make_set(struct
    include Int63
    let size = 63
  end)

module type Graph_s = Graph
  with type node = t
   and type Edge.label = unit

module Graph : Graph_s = struct
  type edge = {
    src : label;
    dst : label;
  } [@@deriving fields]

  let compare_edge x y = match compare_label x.src y.src with
    | 0 -> compare_label x.dst y.dst
    | n -> n

  type arrows = Tree_set.t

  let compare_arrows = Tree_set.compare

  type node_info = {
    inc : arrows;
    out : arrows;
  } [@@deriving compare, fields]

  type graph = node_info Tree.t [@@deriving compare]

  let empty_node = {
    inc = Tree_set.empty;
    out = Tree_set.empty;
  } [@@deriving fields]

  module Node = struct
    type nonrec edge = edge
    type nonrec label = label
    type nonrec graph = graph

    let create = Fn.id
    let label = Fn.id
    let mem n g = Tree.mem g n

    let adj dir n g = Tree.find g n |> function
      | None -> Seq.empty
      | Some ns -> Tree_set.to_sequence (dir ns)

    let succs n = adj out n
    let preds n = adj inc n

    let edges dir reorder n g = Tree.find g n |> function
      | None -> Seq.empty
      | Some ns ->
        Tree_set.to_sequence (dir ns) |>
        Seq.map ~f:(fun m ->
            let src, dst = reorder n m in
            {src; dst})

    let inputs n = edges inc (fun dst src -> src, dst) n
    let outputs n = edges out (fun src dst -> src, dst) n

    let insert n g = Tree.change g n ~f:(function
        | None -> Some empty_node
        | other -> other)

    let insert_arrow field info arrs n =
      if not @@ Tree_set.mem arrs n then
        let arrs = Tree_set.add arrs n in
        Some (Field.fset field info arrs)
      else None

    let remove_arrow field info arrs n =
      let arrs = Tree_set.remove arrs n in
      Some (Field.fset field info arrs)

    let update_arrows update field neibs n g : graph =
      Tree_set.fold neibs ~init:g ~f:(fun g m ->
          Tree.change g m ~f:(function
              | None -> None
              | Some info ->
                update field info (Field.get field info) n))

    let insert_arrows = update_arrows insert_arrow
    let remove_arrows = update_arrows remove_arrow

    let update n l g : graph = Tree.find g n |> function
      | Some {inc; out} when equal_label n l ->
        Tree.set g ~key:l ~data:{inc; out} |>
        insert_arrows Fields_of_node_info.out inc l |>
        insert_arrows Fields_of_node_info.inc out l
      | _ -> g

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
    type t = edge
    type node = Node.t
    type label = unit
    type nonrec graph = graph

    let create src dst () = {src; dst}
    let label _ = ()
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
    let update _ _ g = g

    let remove e g : graph =
      remove_arrow Fields_of_node_info.out e.dst e.src g |>
      remove_arrow Fields_of_node_info.inc e.src e.dst

    include Opaque.Make(struct
        type t = edge [@@deriving compare]
        let hash e = Node.hash e.src lxor Node.hash e.dst
      end)
  end

  type t = graph [@@deriving compare]
  type node = Node.t

  let is_directed = true

  let empty = Tree.empty

  let nodes g = Tree.to_sequence g |> Seq.map ~f:fst
  let edges g = nodes g |> Seq.concat_map ~f:(fun src -> Node.outputs src g)
  let number_of_nodes g = Tree.length g

  let number_of_edges g =
    Tree.fold g ~init:0 ~f:(fun ~key:_ ~data:{out; _} sum ->
        sum + Tree_set.length out)

  include Opaque.Make(struct
      type t = graph [@@deriving compare]
      let hash g =
        nodes g |> Seq.fold ~init:0 ~f:(fun hash n ->
            Node.hash n lxor hash)
    end)

  include Printable.Make(struct
      type nonrec t = t
      let module_name = None

      let pp ppf graph =
        let open Graphlib in
        let string_of_node =
          by_given_order symbols Node.compare (nodes graph) in
        Dot.pp_graph
          ~string_of_node
          ~nodes_of_edge:(fun e -> Edge.(src e, dst e))
          ~nodes:(nodes graph)
          ~edges:(edges graph)
          ppf
    end)
end

module Pseudo(G : Graph_s) = struct
  let connect_with_entry n =
    if n = pseudoentry then Fn.id
    else G.Edge.(insert (create pseudoentry n ()))

  let connect_with_exit n =
    if n = pseudoexit then Fn.id
    else G.Edge.(insert (create n pseudoexit ()))

  let if_unreachable ~from connect g n =
    match G.Node.degree ~dir:from n g with
    | 0 -> connect n
    | _ -> Fn.id

  let connect_unreachable g n =
    if_unreachable ~from:`Out connect_with_exit  g n @@
    if_unreachable ~from:`In  connect_with_entry g n @@
    g

  let add g =
    G.nodes g |> Seq.fold ~init:g ~f:connect_unreachable |> fun g ->
    Graphlib.depth_first_search (module G) g
      ~init:g ~start:pseudoentry
      ~start_tree:connect_with_entry |> fun g ->
    Graphlib.depth_first_search (module G) g
      ~rev:true ~init:g ~start:pseudoexit
      ~start_tree:connect_with_exit
end
