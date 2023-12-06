open Core
open Graphlib.Std
open Regular.Std

module G = Graphlib.Make(Label)(Edge)

module Pseudo = Label.Pseudo(struct
    include G
    let e = `always
  end)

let insert_br b l e g = match G.Node.edge b l g with
  | None -> G.Edge.(insert (create b l e) g)
  | Some n -> match G.Edge.label n, e with
    | `true_ _, `false_ _
    | `false_ _, `true_ _ ->
      let g = G.Edge.remove n g in
      G.Edge.(insert (create b l `always) g)
    | _ -> g

let insert_sw b l x v g = match G.Node.edge b l g with
  | None -> G.Edge.(insert (create b l @@ `switch (x, [v], false)) g)
  | Some n -> match G.Edge.label n with
    | `default x ->
      let g = G.Edge.remove n g in
      G.Edge.(insert (create b l @@ `switch (x, [v], true)) g)
    | `switch (x, vs, def) ->
      let g = G.Edge.remove n g in
      G.Edge.(insert (create b l @@ `switch (x, v :: vs, def)) g)
    | _ -> g

let accum_sw ~key ~data b x g = match data with
  | `label (l, _) -> insert_sw b l x key g

let accum g b : Ctrl.t -> G.t = function
  | `hlt -> g
  | `jmp (`label (l, _)) -> G.Edge.(insert (create b l `always) g)
  | `jmp _ -> g
  | `br (x, `label (t, _), `label (f, _)) ->
    insert_br b f (`false_ x) @@
    insert_br b t (`true_ x) g
  | `br (x, `label (l, _), _) ->
    insert_br b l (`true_ x ) g
  | `br (x, _, `label (l, _)) ->
    insert_br b l (`false_ x) g
  | `br _ -> g
  | `ret _ -> g
  | `sw (_, x, `label (d, _), t) ->
    let init = G.Edge.(insert (create b d @@ `default x) g) in
    Map.fold_right t.tbl ~init ~f:(accum_sw b x)

let create fn =
  Func.blks fn |> Seq.fold ~init:G.empty ~f:(fun g b ->
      let l = Blk.label b and c = Blk.ctrl b in
      accum (G.Node.insert l g) l c) |> Pseudo.add

include G
