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

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let module S = Slot_initialization.Make(Scalars_common.VL) in
    let slots = S.Analysis.collect_slots fn in
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let s = S.analyze cfg blks slots in
    let undef l = Hash_set.mem s.bad l in
    V.run fn ~undef >>= Ssa.run
  else
    E.failf
      "In Promote_slots: expected SSA form for function $%s"
      (Func.name fn) ()

let run_abi fn =
  let open Abi in
  if Dict.mem (Func.dict fn) Tags.ssa then
    let module S = Slot_initialization.Make(Scalars_common.AL) in
    let slots = S.Analysis.collect_slots fn in
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let s = S.analyze cfg blks slots in
    let undef l = Hash_set.mem s.bad l in
    A.run fn ~undef >>= Ssa.run_abi
  else
    E.failf
      "In Promote_slots (ABI): expected SSA form for function $%s"
      (Func.name fn) ()
