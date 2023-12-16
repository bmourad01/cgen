open Core
open Graphlib.Std
open Regular.Std

module T = struct
  type t = Int63.t [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pseudoentry = Int63.(zero - of_int 2)
let pseudoexit = Int63.succ pseudoentry
let is_pseudo l = Int63.(l = pseudoentry || l = pseudoexit)

let pp ppf = function
  | l when Int63.(l = pseudoentry) -> Format.fprintf ppf "@pseudoentry"
  | l when Int63.(l = pseudoexit) -> Format.fprintf ppf "@pseudoexit"
  | l -> Format.fprintf ppf "@%a" Int63.pp l

include Regular.Make(struct
    include T
    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Label"
  end)

module Tree = Patricia_tree.Make(struct
    include Int63
    let size = 63
    let to_int = to_int_trunc
  end)

module type Graph = Graph
  with type node = t
   and type Edge.label = unit

module Pseudo(G : Graph) = struct
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
