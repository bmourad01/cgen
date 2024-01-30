open Core
open Graphlib.Std
open Regular.Std

module Blk = Virtual_blk
module Ctrl = Virtual_ctrl
module Func = Virtual_func
module G = Graphlib.Make(Label)(Unit)
module Pseudo = Label.Pseudo(G)

let accum tbl g b : _ -> G.t = function
  | `hlt -> g
  | `jmp (`label (l, _)) -> G.Edge.(insert (create b l ()) g)
  | `jmp _ -> g
  | `br (_, `label (t, _), `label (f, _)) ->
    G.Edge.(insert (create b t ()) @@
            insert (create b f ()) g)
  | `br (_, `label (l, _), _) | `br (_, _, `label (l, _)) ->
    G.Edge.(insert (create b l ()) g)
  | `br _ -> g
  | `ret _ -> g
  | `sw (_, _, `label (d, _), t) ->
    let init = G.Edge.(insert (create b d ()) g) in
    tbl t |> Seq.fold ~init
      ~f:(fun g (_, `label (l, _)) ->
          G.Edge.(insert (create b l ()) g))

let create fn =
  Func.blks fn |> Seq.fold ~init:G.empty ~f:(fun g b ->
      let l = Blk.label b and c = Blk.ctrl b in
      accum Ctrl.Table.enum (G.Node.insert l g) l c) |> Pseudo.add

include G
