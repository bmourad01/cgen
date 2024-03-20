open Virtual
open Promote_slots_impl

let store op i = match op i with
  | `store (t, v, `var a) -> Some (v, a, t)
  | _ -> None

let load op i = match op i with
  | `load (x, t, _) -> Some (x, t)
  | _ -> None

let fibits x f a = `uop (x, `fibits f, a)
let ifbits x i a = `uop (x, `ifbits i, a)
let copy   x t a = `uop (x, `copy t, a)

module V = Make(struct
    type lhs = Var.t option
    module Insn = struct
      include Insn
      let store = store op
      let load = load op
      let fibits = fibits
      let ifbits = ifbits
      let copy = copy
    end
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
    module Use = Use
    module Resolver = Resolver
  end)

open E.Syntax

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    V.run fn >>= Ssa.run
  else
    E.failf
      "In Promote_slots: expected SSA form for function $%s"
      (Func.name fn) ()
