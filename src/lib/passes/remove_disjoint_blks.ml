open Core
open Graphlib.Std
open Regular.Std
open Virtual

exception Done of Label.Set.t

let dfs cfg start =
  Graphlib.depth_first_search (module Cfg) cfg ~start
    ~init:Label.Set.empty
    ~start_tree:(fun n s ->
        if Label.(n = start) then s else raise @@ Done s)
    ~enter_node:(fun _ n s -> Set.add s n)

let reachable fn =
  let cfg = Cfg.create fn in
  let start = Func.entry fn in
  try dfs cfg start with Done s -> s

let run fn =
  Func.blks fn |> Seq.map ~f:Blk.label |>
  Seq.filter ~f:(Fn.non @@ Set.mem @@ reachable fn) |>
  Seq.fold ~init:fn ~f:Func.remove_blk_exn
