open Core
open Regular.Std

module Func = Structured_func
module Stmt = Structured_stmt

open Context.Syntax

type transl = {
  ivec         : Virtual.insn Vec.t; (* Pending instructions to be committed. *)
  mutable bvec : Virtual.blk Vec.t;  (* Pending blocks to be committed. *)
  mutable blk  : Label.t;            (* Label of current block. *)
}

let commit ?cont t ctrl =
  let insns = Vec.to_list t.ivec in
  Vec.clear t.ivec;
  let blk = Virtual.Blk.create ~label:t.blk ~insns ~ctrl () in
  Vec.push t.bvec blk;
  Option.iter cont ~f:(fun l -> t.blk <- l)

let transl_op op = Context.Virtual.insn op

let transl_cond t : Stmt.cond -> Var.t Context.t = function
  | `var x -> !!x
  | `cmp (k, l, r) ->
    let* x = Context.Var.fresh in
    let op = `bop (x, (k :> Virtual.Insn.binop), l, r) in
    let+ i = transl_op op in
    Vec.push t.ivec i;
    x

let local l = `label (l, [])

let rec transl_stmt t s k =
  match (s : Stmt.t) with
  | #Virtual.Insn.op as op ->
    let* i = transl_op op in
    k @@ Vec.push t.ivec i
  | `nop -> !!()
  | `seq (s1, s2) ->
    transl_stmt t s1 @@ fun _ ->
    transl_stmt t s2 k
  | `ite (c, y, n) ->
    let* c = transl_cond t c in
    let* ky = Context.Label.fresh in
    let* kn = Context.Label.fresh in
    let ctrl = `br (c, local ky, local kn) in
    commit ~cont:ky t ctrl;
    transl_stmt t y @@ fun _ ->
    transl_stmt t n k
  | `loop _ -> !!()
  | `break -> !!()
  | `continue -> !!()
  | `sw _ -> !!()
  | `label _ -> !!()
  | `goto _ -> !!()
  | `hlt -> !!()
  | `ret _ -> !!()
