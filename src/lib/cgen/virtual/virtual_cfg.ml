open Core
open Regular.Std

module Blk = Virtual_blk
module Ctrl = Virtual_ctrl
module Func = Virtual_func
module G = Label.Graph
module Pseudo = Label.Pseudo(G)

let create fn =
  Func.fold_blks fn
    ~init:G.empty ~f:(fun g b ->
        let src = Blk.label b
        and c = Blk.ctrl b in
        Ctrl.fold_dests c
          ~init:(G.Node.insert src g)
          ~f:(fun g dst ->
              let e = G.Edge.create src dst () in
              G.Edge.insert e g)) |> Pseudo.add

include G
