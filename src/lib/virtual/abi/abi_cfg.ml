open Core
open Regular.Std

module Cfg = Virtual_cfg

let create fn =
  Abi_func.blks fn |> Seq.fold ~init:Cfg.G.empty ~f:(fun g b ->
      let l = Abi_blk.label b and c = Abi_blk.ctrl b in
      Cfg.accum Abi_ctrl.Table.enum (Cfg.G.Node.insert l g) l c) |>
  Cfg.Pseudo.add

include Cfg.G
