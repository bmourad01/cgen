open Core
open Virtual
open Sroa_impl
open Sroa_coalesce_common

module V = Make(VL)
module A = Make(AL)

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
