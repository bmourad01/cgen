open Core
open Virtual
open Simplify_cfg_common

module Ifc = Simplify_cfg_ifc
module Brsel = Simplify_cfg_brsel
module Merge_blks = Simplify_cfg_merge_blks
module Contract = Simplify_cfg_contract
module Merge_rets = Simplify_cfg_merge_rets
module Two_case_switch = Simplify_cfg_two_case_switch
module Tailrec = Simplify_cfg_tailrec
module Short_circ = Simplify_cfg_short_circ
module Duplicate_br = Simplify_cfg_duplicate_br

let try_ f = try f () with
  | Invalid_argument msg
  | Failure msg -> Context.failf "In Simplify_cfg: %s" msg ()

open Context.Syntax

let run tenv fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let env = init fn in
    let rec loop fn =
      let* brsel = Brsel.run tenv env fn in
      if Merge_blks.run env
      || Contract.run env
      || Short_circ.run env
      || Duplicate_br.run env
      || Ifc.run tenv env fn
      || brsel
      then loop @@ recompute_cfg env @@ update_fn env fn
      else !!fn in
    try_ @@ fun () ->
    (* This only needs to run once at the beginning, since it
       affects downstream passes but itself is not affected
       by any other changes we're doing. *)
    let* fn = Merge_rets.run tenv env fn in
    (* Run the fixpoint loop. *)
    let* fn = loop fn in
    (* The last two passes don't need to run in fixpoint, but
       they benefit from the previous changes. *)
    Two_case_switch.go fn >>= Tailrec.go env
  else
    Context.failf
      "In Simplify_cfg: expected SSA form for function $%s"
      (Func.name fn) ()
