open Core
open Virtual
open Simplify_cfg_common

module Subst = Simplify_cfg_subst
module Merge_blks = Simplify_cfg_merge_blks
module Contract = Simplify_cfg_contract
module Merge_rets = Simplify_cfg_merge_rets
module Two_case_switch = Simplify_cfg_two_case_switch
module Tailrec = Simplify_cfg_tailrec

let try_ f = try f () with
  | Invalid_argument msg
  | Failure msg -> Context.failf "In Simplify_cfg: %s" msg ()

open Context.Syntax

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let env = init fn in
    let upd = update_fn env in
    let rec loop fn =
      let merged = Merge_blks.run env in
      if Contract.run env
      || Merge_rets.run env then
        loop @@ recompute_cfg env @@ upd fn
      else if merged then upd fn
      else fn in
    try_ @@ fun () -> (Two_case_switch.go @@ loop fn) >>= Tailrec.go
  else
    Context.failf
      "In Simplify_cfg: expected SSA form for function $%s"
      (Func.name fn) ()
