open Core
open Regular.Std

module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func

module G = Label.Graph
module Pseudo = Label.Pseudo(G)

let check fn =
  if Dict.mem (Func.dict fn) Tags.peephole then
    invalid_argf "Function $%s has gone through peephole optimization: \
                  cannot compute CFG" (Func.name fn) ()

let create ~dests fn =
  check fn;
  Func.blks fn |> Seq.fold ~init:G.empty ~f:(fun g b ->
      let s = Blk.label b in
      let g = G.Node.insert s g in
      Blk.insns b |> Seq.fold ~init:g ~f:(fun g i ->
          dests (Insn.insn i) |> Set.fold ~init:g ~f:(fun g d ->
              let g = G.Node.insert d g in
              G.Edge.(insert (create s d ()) g)))) |> Pseudo.add

include G
