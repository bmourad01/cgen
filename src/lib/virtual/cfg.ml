open Core
open Graphlib.Std
open Regular.Std

module G = Graphlib.Make(Label)(Edge)

let connect_with_entry n =
  let e = Label.pseudoentry in
  if Label.(n = e) then Fn.id
  else G.Edge.(insert (create e n `always))

let connect_with_exit n =
  let e = Label.pseudoexit in
  if Label.(n = e) then Fn.id
  else G.Edge.(insert (create n e `always))

let if_unreachable ~from connect g n =
  if G.Node.degree ~dir:from n g = 0 then connect n else Fn.id

let accum g b : Insn.Ctrl.t -> G.t = function
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
    Map.fold t ~init ~f:(fun ~key:v ~data:(`label (l, _)) g ->
        G.Edge.(insert (create b l @@ `switch (x, v)) g))

let connect_unreachable g n =
  if_unreachable ~from:`Out connect_with_exit  g n @@
  if_unreachable ~from:`In  connect_with_entry g n @@
  g

let create fn =
  Func.blks fn |> Seq.fold ~init:G.empty ~f:(fun g b ->
      let l = Blk.label b and c = Blk.ctrl b in
      accum (G.Node.insert l g) l c) |> fun g ->
  G.nodes g |> Seq.fold ~init:g ~f:connect_unreachable |> fun g ->
  Graphlib.depth_first_search (module G) g
    ~init:g ~start:Label.pseudoentry
    ~start_tree:connect_with_entry |> fun g ->
  Graphlib.depth_first_search (module G) g
    ~rev:true ~init:g ~start:Label.pseudoexit
    ~start_tree:connect_with_exit

include G
