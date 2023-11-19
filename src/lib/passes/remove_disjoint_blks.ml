open Core
open Graphlib.Std
open Regular.Std
open Virtual

let reachable fn = with_return @@ fun {return} ->
  let cfg = Cfg.create fn in
  let start = Func.entry fn in
  Graphlib.depth_first_search (module Cfg) cfg ~start
    ~init:Label.Set.empty
    ~start_tree:(fun n s ->
        if Label.(n = start) then s else return s)
    ~enter_node:(fun _ n s -> Set.add s n)

let run fn =
  Func.blks fn |> Seq.map ~f:Blk.label |>
  Seq.filter ~f:(Fn.non @@ Set.mem @@ reachable fn) |>
  Seq.to_list |> Func.remove_blks_exn fn
