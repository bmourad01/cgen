open Core
open Graphlib.Std
open Regular.Std
open Virtual

(* Unreachable blocks (excluding the entry block) will have
   only one predecessor, which is the pseudoentry label. *)
let unreachable l cfg =
  Cfg.Node.preds l cfg |>
  Seq.filter ~f:(Fn.non Label.is_pseudo) |>
  Seq.is_empty

let run fn =
  let cfg = Cfg.create fn in
  let entry = Func.entry fn in
  Func.blks fn |> Seq.map ~f:Blk.label |> Seq.filter ~f:(fun l ->
      Label.(l <> entry) && unreachable l cfg) |>
  Seq.fold ~init:fn ~f:Func.remove_blk_exn
