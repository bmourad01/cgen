open Core
open Virtual
open Sroa_impl

module V = Make(struct
    module Insn = struct
      type t = Insn.t
      type op = Insn.op

      let op = Insn.op
      let label = Insn.label

      let load_or_store_to (o : op) = match o with
        | `load (_, (#Type.basic as ty), `var x) -> Some (x, ty)
        | `store ((#Type.basic as ty), _, `var x) -> Some (x, ty)
        | _ -> None

      let subst_load_or_store (o : op) ~f = match o with
        | `load (x, ty, `var a) -> `load (x, ty, `var (f a))
        | `store (ty, v, `var a) -> `store (ty, v, `var (f a))
        | op -> op

      let offset (o : op) = match o with
        | `bop (_, `add _, `var x, `int (i, _))
        | `bop (_, `add _, `int (i, _), `var x) ->
          Some (x, Bv.to_int64 i)
        | `bop (_, `sub _, `var x, `int (i, _)) ->
          Some (x, Int64.neg @@ Bv.to_int64 i)
        | _ -> None

      let lhs = Insn.lhs_of_op
      let free_vars = Insn.free_vars_of_op
    end

    module Ctrl = Ctrl
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
