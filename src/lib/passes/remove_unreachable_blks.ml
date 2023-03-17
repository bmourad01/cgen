open Core
open Graphlib.Std
open Regular.Std
open Virtual

let run fn =
  let cfg = Cfg.create fn in
  let entry = Func.entry fn in
  Func.blks fn |> Seq.fold ~init:Label.Set.empty ~f:(fun acc blk ->
      let l = Blk.label blk in
      if Label.(l <> entry) then
        Cfg.Node.preds l cfg |>
        Seq.filter ~f:(Fn.non Label.is_pseudo) |>
        Seq.is_empty |> function
        | true -> Set.add acc l
        | false -> acc
      else acc) |>
  Set.fold ~init:fn ~f:Func.remove_blk_exn
