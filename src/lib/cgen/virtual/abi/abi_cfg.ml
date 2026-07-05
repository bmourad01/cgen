open Core

module Cfg = Virtual_cfg

let create fn =
  Abi_func.fold_blks fn
    ~init:Cfg.G.empty ~f:(fun g b ->
        let src = Abi_blk.label b
        and c = Abi_blk.ctrl b in
        Abi_ctrl.fold_dests c
          ~init:(Cfg.G.Node.insert src g)
          ~f:(fun g dst ->
              let e = Cfg.G.Edge.create src dst in
              Cfg.G.Edge.insert e g)) |> Cfg.Pseudo.add

include Cfg.G
