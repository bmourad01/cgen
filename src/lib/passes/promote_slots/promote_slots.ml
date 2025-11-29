open Core
open Virtual
open Promote_slots_impl

let store op i = match op i with
  | `store ((#Type.basic as t), v, `var a) -> Some (v, a, t)
  | _ -> None

let load op i = match op i with
  | `load (x, (#Type.basic as t), _) -> Some (x, t)
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
    module Resolver = Resolver
  end)

module A = Make(struct
    type lhs = Var.Set.t
    module Insn = struct
      include Abi.Insn
      let store = store op
      let load = load op
      let fibits = fibits
      let ifbits = ifbits
      let copy = copy
    end
    module Blk = Abi.Blk
    module Func = Abi.Func
    module Cfg = Abi.Cfg
    module Resolver = Abi.Resolver
  end)

open E.Syntax

let apply
    (type fn)
    (module M : Scalars.L with type Func.t = fn)
    run ssa (fn : fn) =
  let module Sinit = Slot_initialization.Make(M) in
  let slots = Sinit.S.collect_slots fn in
  let cfg = M.Cfg.create fn in
  let blks = M.Func.map_of_blks fn in
  let s = Sinit.analyze cfg blks slots in
  let undef l = Hash_set.mem s.bad l in
  run fn ~undef >>= ssa

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    apply (module Scalars_common.VL) V.run Ssa.run fn
  else
    E.failf
      "In Promote_slots: expected SSA form for function $%s"
      (Func.name fn) ()

let run_abi fn =
  let open Abi in
  if Dict.mem (Func.dict fn) Tags.ssa then
    apply (module Scalars_common.AL) A.run Ssa.run_abi fn
  else
    E.failf
      "In Promote_slots (ABI): expected SSA form for function $%s"
      (Func.name fn) ()
