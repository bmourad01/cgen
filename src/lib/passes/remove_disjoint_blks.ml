open Core
open Graphlib.Std
open Regular.Std
open Virtual

let reachable fn =
  let cfg = Cfg.create fn in
  Graphlib.depth_first_search (module Cfg) cfg
    ~start:(Func.entry fn)
    ~init:Label.Set.empty
    ~enter_node:(fun _ n s -> Set.add s n)

let run fn =
  Func.blks fn |> Seq.map ~f:Blk.label |>
  Seq.filter ~f:(Fn.non @@ Set.mem @@ reachable fn) |>
  Seq.fold ~init:fn ~f:Func.remove_blk_exn
