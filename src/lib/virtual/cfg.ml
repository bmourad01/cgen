open Core
open Graphlib.Std
open Regular.Std

module G = Graphlib.Make(Label)(Edge)

module Pseudo = Label.Pseudo(struct
    include G
    let e = `always
  end)

let accum g b : Ctrl.t -> G.t = function
  | `hlt -> g
  | `jmp (`label (l, _)) -> G.Edge.(insert (create b l `always) g)
  | `jmp _ -> g
  | `br (x, `label (t, _), `label (f, _)) ->
    let et = G.Edge.create b t @@  `true_ x in
    let ef = G.Edge.create b f @@ `false_ x in
    G.Edge.(insert ef (insert et g))
  | `br (x, `label (l, _), _) -> G.Edge.(insert (create b l @@  `true_ x) g)
  | `br (x, _, `label (l, _)) -> G.Edge.(insert (create b l @@ `false_ x) g)
  | `br _ -> g
  | `ret _ -> g
  | `sw (_, x, `label (d, _), t) ->
    let init = G.Edge.(insert (create b d @@ `default x) g) in
    Map.fold t.tbl ~init ~f:(fun ~key:v ~data:(`label (l, _)) g ->
        G.Edge.(insert (create b l @@ `switch (x, v)) g))

let create fn =
  Func.blks fn |> Seq.fold ~init:G.empty ~f:(fun g b ->
      let l = Blk.label b and c = Blk.ctrl b in
      accum (G.Node.insert l g) l c) |> Pseudo.add

include G
