module Var = Context_var
module Label = Context_label
module M = Context_common.M

open M.Syntax

let insn ?(dict = Dict.empty) op =
  let+ label = Label.fresh in
  Virtual.Abi.Insn.create op ~label ~dict

let binop ?(dict = Dict.empty) b l r =
  let* var = Var.fresh in
  let+ i = insn (`bop (var, b, l, r)) ~dict in
  var, i

let unop ?(dict = Dict.empty) u a =
  let* var = Var.fresh in
  let+ i = insn (`uop (var, u, a)) ~dict in
  var, i

let sel ?(dict = Dict.empty) t c y n =
  let* var = Var.fresh in
  let+ i = insn (`sel (var, t, c, y, n)) ~dict in
  var, i

let call ?(dict = Dict.empty) rs f args =
  let* xs = M.List.map rs ~f:(fun (t, r) ->
      let+ x = Var.fresh in
      x, t, r) in
  let+ i = insn (`call (xs, f, args)) ~dict in
  xs, i

let load ?(dict = Dict.empty) t a =
  let* var = Var.fresh in
  let+ i = insn (`load (var, t, a)) ~dict in
  var, i

let store ?(dict = Dict.empty) t v a =
  insn (`store (t, v, a)) ~dict

let loadreg ?(dict = Dict.empty) t r =
  let* var = Var.fresh in
  let+ i = insn (`loadreg (var, t, r)) ~dict in
  var, i

let storereg ?(dict = Dict.empty) r a =
  insn (`storereg (r, a)) ~dict

let setreg ?(dict = Dict.empty) r a =
  insn (`setreg (r, a)) ~dict

let stkargs ?(dict = Dict.empty) () =
  let* var = Var.fresh in
  let+ i = insn (`stkargs var) ~dict in
  var, i

module Blit = Context_virtual.Make_blit(struct
    type insn = Virtual.Abi.insn
    let add ty x y = binop (`add ty) x y
    let load ty a = load (ty :> Type.basic) a
    let store ty v a = store (ty :> Type.basic) v a
  end)

let blit ~src ~dst word size = Blit.go word src dst size
let ldm word src size = Blit.go word src src size ~ignore_dst:true
