open Core
open Monads.Std
open Regular.Std
open Virtual
open Scalars
open Coalesce_slots_impl
open Sroa_coalesce_common

module E = Monad.Result.Error

module V = Make(struct
    module Insn = struct
      type t = Insn.t
      type op = Insn.op
      let create ~label op = Insn.create op ~label
      let with_op = Insn.with_op
      let op = Insn.op
      let special = function
        | #Insn.variadic -> true
        | _ -> false
      let label = Insn.label
      let lhs = var_set_of_option @. Insn.lhs_of_op
      let offset = (offset :> op -> _)
      let copy_of = (copy_of :> op -> _)
      let free_vars = Insn.free_vars_of_op
      let escapes = (escapes is_named free_vars :> op -> _)
      let load_or_store_to = (load_or_store_to :> op -> _)
      let replace_load_or_store_addr a = (replace_load_or_store_addr a :> op -> _)
      let add x ty b o = (add x ty b o :> op)
    end
    module Ctrl = struct
      type t = ctrl
      let free_vars = Ctrl.free_vars
      let escapes = (escapes_ctrl free_vars :> t -> _)
      let locals = (locals Ctrl.Table.enum :> t -> _)
    end
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)

module A = Make(struct
    open Abi
    module Insn = struct
      type t = Insn.t
      type op = Insn.op
      let create ~label op = Insn.create op ~label
      let with_op = Insn.with_op
      let op = Insn.op
      let special = function
        | #Insn.extra -> true
        | _ -> false
      let label = Insn.label
      let lhs = Insn.def_of_op
      let offset = (offset :> op -> _)
      let copy_of = (copy_of :> op -> _)
      let free_vars = Insn.free_vars_of_op
      let escapes = (escapes (const false) free_vars :> op -> _)
      let load_or_store_to = (load_or_store_to :> op -> _)
      let replace_load_or_store_addr a = (replace_load_or_store_addr a :> op -> _)
      let add x ty b o = (add x ty b o :> op)
    end
    module Ctrl = struct
      type t = ctrl
      let free_vars = Ctrl.free_vars
      let escapes = (escapes_ctrl free_vars :> t -> _)
      let locals = (locals Ctrl.Table.enum :> t -> _)
    end
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)

open E.Let

let check_ssa msg n d =
  if Dict.mem d Tags.ssa then Ok ()
  else E.failf "In Coalesce_slots%s: function $%s is not in SSA form" msg n ()

let no_deads f d is = List.filter is ~f:(not @. Lset.mem d @. f)

let run fn =
  let+ () = check_ssa "" (Func.name fn) (Func.dict fn) in
  let t = V.run fn in
  if is_empty t then fn else
    let f =
      if Map.is_empty t.subst then
        fun b ->
          Blk.insns b |> Seq.to_list |>
          no_deads Insn.label t.deads |>
          Blk.with_insns b
      else
        fun b ->
          let insns, ctrl = Subst_mapper.map_blk t.subst b in
          let insns = no_deads Insn.label t.deads insns in
          Blk.with_ctrl (Blk.with_insns b insns) ctrl in
    Func.map_blks fn ~f

let run_abi fn =
  let+ () = check_ssa " (ABI)" (Abi.Func.name fn) (Abi.Func.dict fn) in
  let t = A.run fn in
  if is_empty t then fn else
    let f =
      if Map.is_empty t.subst then
        fun b ->
          Abi.Blk.insns b |> Seq.to_list |>
          no_deads Abi.Insn.label t.deads |>
          Abi.Blk.with_insns b
      else
        fun b ->
          let insns, ctrl = Subst_mapper_abi.map_blk t.subst b in
          let insns = no_deads Abi.Insn.label t.deads insns in
          Abi.Blk.with_ctrl (Abi.Blk.with_insns b insns) ctrl in
    Abi.Func.map_blks fn ~f
