open Core
open Regular.Std
open Graphlib.Std

module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func

module G = Graphlib.Make(Label)(Unit)
module Pseudo = Label.Pseudo(G)

let create ~dests fn =
  Func.blks fn |> Seq.fold ~init:G.empty ~f:(fun g b ->
      let s = Blk.label b in
      Blk.insns b |> Seq.fold ~init:g ~f:(fun g i ->
          dests (Insn.insn i) |> Set.fold ~init:g ~f:(fun g d ->
              G.Edge.(insert (create s d ()) g)))) |> Pseudo.add

include G
