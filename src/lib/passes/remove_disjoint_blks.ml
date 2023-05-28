open Core
open Graphlib.Std
open Regular.Std
open Virtual

let reachable fn =
  let cfg = Cfg.create fn in
  let entry = Func.entry fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  Tree.descendants dom entry |>
  Label.Set.of_sequence |>
  Fn.flip Set.add entry

let run fn =
  Func.blks fn |> Seq.map ~f:Blk.label |>
  Seq.filter ~f:(Fn.non @@ Set.mem @@ reachable fn) |>
  Seq.fold ~init:fn ~f:Func.remove_blk_exn
