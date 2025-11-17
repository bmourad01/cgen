open Core
open Monads.Std
open Regular.Std
open Virtual
open Scalars
open Coalesce_slots_impl
open Sroa_coalesce_common

module E = Monad.Result.Error

module V = Make(VL)
module A = Make(AL)

open E.Let

let check_ssa msg n d =
  if Dict.mem d Tags.ssa then Ok ()
  else E.failf "In Coalesce_slots%s: function $%s is not in SSA form" msg n ()

let apply t fn map_blks map_blk insns with_insns with_ctrl label =
  let not_dead = not @. Lset.mem t.deads @. label in
  if is_empty t then fn else
    let f = if Map.is_empty t.subst then fun b ->
        insns b |> Seq.filter ~f:not_dead |>
        Seq.to_list |> with_insns b
      else fun b ->
        let is, c = map_blk t.subst b in
        let is = if Lset.is_empty t.deads then is
          else List.filter is ~f:not_dead in
        with_ctrl (with_insns b is) c in
    map_blks fn ~f
[@@specialise]

let run fn =
  let+ () = check_ssa "" (Func.name fn) (Func.dict fn) in
  let t = V.run fn in
  apply t fn
    Func.map_blks
    Subst_mapper.map_blk
    Blk.insns
    Blk.with_insns
    Blk.with_ctrl
    Insn.label

let run_abi fn =
  let open Abi in
  let+ () = check_ssa " (ABI)" (Func.name fn) (Func.dict fn) in
  let t = A.run fn in
  apply t fn
    Func.map_blks
    Subst_mapper_abi.map_blk
    Blk.insns
    Blk.with_insns
    Blk.with_ctrl
    Insn.label
