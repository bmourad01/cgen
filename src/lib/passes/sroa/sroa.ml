open Core
open Virtual
open Scalars
open Sroa_impl
open Sroa_coalesce_common

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

open Context.Syntax

let run fn =
  let* () = Context.unless (Dict.mem (Func.dict fn) Tags.ssa) @@ fun () ->
    Context.failf "In SROA: function $%s is not in SSA form"
      (Func.name fn) () in
  V.run fn

let run_abi fn =
  let* () = Context.unless (Dict.mem (Abi.Func.dict fn) Tags.ssa) @@ fun () ->
    Context.failf "In SROA (ABI): function $%s is not in SSA form"
      (Abi.Func.name fn) () in
  A.run fn
