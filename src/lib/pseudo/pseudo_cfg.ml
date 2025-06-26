open Core
open Regular.Std

module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func

module G = Label.Graph
module Pseudo = Label.Pseudo(G)

let create ~is_barrier ~dests fn =
  let afters = Func.collect_afters fn in
  Func.blks fn |> Seq.fold ~init:G.empty ~f:(fun g b ->
      let s = Blk.label b in
      let g = G.Node.insert s g in
      let g = Blk.insns b |> Seq.fold ~init:g ~f:(fun g i ->
          dests (Insn.insn i) |> Set.fold ~init:g ~f:(fun g d ->
              let g = G.Node.insert d g in
              G.Edge.(insert (create s d ()) g))) in
      Blk.insns b ~rev:true |> Seq.hd |> function
      | Some i when is_barrier @@ Insn.insn i -> g
      | Some _ | None ->
        Label.Tree.find afters s |>
        Option.value_map ~default:g ~f:(fun a ->
            G.Edge.(insert (create s a ()) g))) |> Pseudo.add

include G
