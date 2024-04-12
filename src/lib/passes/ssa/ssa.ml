open Core
open Virtual
open Ssa_impl

let args_of_vars = List.map ~f:(fun x -> `var x)

let argify_local ~inc : local -> local = function
  | `label (l, args) ->
    `label (l, args_of_vars (inc l) @ args)

let argify_dst ~inc : dst -> dst = function
  | #local as l -> (argify_local ~inc l :> dst)
  | d -> d

let argify_tbl ~inc =
  Ctrl.Table.map_exn ~f:(fun v l -> v, argify_local ~inc l)

let argify_ctrl ~inc c =
  let loc = argify_local ~inc in
  let dst = argify_dst ~inc in
  match c with
  | `hlt -> c
  | `jmp d -> `jmp (dst d)
  | `br (c, t, f) -> `br (c, dst t, dst f)
  | `ret _ -> c
  | `sw (t, i, d, tbl) -> `sw (t, i, loc d, argify_tbl ~inc tbl)

let rename_operand ~stk : operand -> operand = function
  | `var x -> `var (stk x)
  | o -> o

let rename_global ~stk : global -> global = function
  | `var x -> `var (stk x)
  | g -> g

let rename_local ~stk : local -> local = function
  | `label (l, args) ->
    `label (l, List.map args ~f:(rename_operand ~stk))

let rename_dst ~stk : dst -> dst = function
  | #global as g -> (rename_global ~stk g :> dst)
  | #local  as l -> (rename_local  ~stk l :> dst)

let rename_tbl ~stk =
  Ctrl.Table.map_exn ~f:(fun v l -> v, rename_local ~stk l)

let swindex ~stk = function
  | `var x -> `var (stk x)
  | `sym _ as s -> s

module V = Make(struct
    type lhs = Var.t option

    module Insn = struct
      include Insn
      let lhs = Fn.compose Option.to_list Insn.lhs
    end

    module Ctrl = Ctrl
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
    module Live = Live
    module Resolver = Resolver

    let argify_ctrl = argify_ctrl

    let acall ~rename =
      Option.map ~f:(fun (x, t) -> rename x, t)

    let rename_op ~stk ~rename op =
      let glo = rename_global ~stk in
      let opnd = rename_operand ~stk in
      let args = List.map ~f:opnd in
      match (op : Insn.op) with
      | `call (r, f, a, va) ->
        let f = glo f in
        let a = args a in
        let va = args va in
        let r = acall ~rename r in
        `call (r, f, a, va)
      | `vaarg (x, t, y) ->
        let y = glo y in
        let x = rename x in
        `vaarg (x, t, y)
      | `vastart x -> `vastart (glo x)
      | `bop (x, b, l, r) ->
        let l = opnd l in
        let r = opnd r in
        let x = rename x in
        `bop (x, b, l, r)
      | `uop (x, u, a) ->
        let a = opnd a in
        let x = rename x in
        `uop (x, u, a)
      | `sel (x, t, c, l, r) ->
        let c = stk c in
        let l = opnd l in
        let r = opnd r in
        let x = rename x in
        `sel (x, t, c, l, r)
      | `load (x, t, a) ->
        let a = opnd a in
        let x = rename x in
        `load (x, t, a)
      | `store (t, v, a) -> `store (t, opnd v, opnd a)

    let rename_ctrl ~stk c =
      let dst = rename_dst ~stk in
      let loc = rename_local ~stk in
      let opnd = rename_operand ~stk in
      match c with
      | `hlt -> `hlt
      | `jmp d -> `jmp (dst d)
      | `br (c, t, f) -> `br (stk c, dst t, dst f)
      | `ret r -> `ret (Option.map r ~f:opnd)
      | `sw (t, i, d, tbl) -> `sw (t, swindex ~stk i, loc d, rename_tbl ~stk tbl)

  end)

let run = V.run
let check = V.check
