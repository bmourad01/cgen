open Virtual

module Params = Lower_abi_params
module Refs = Lower_abi_refs
module Rets = Lower_abi_rets
module Calls = Lower_abi_calls
module Vastart = Lower_abi_vastart
module Vaarg = Lower_abi_vaarg
module Translate = Lower_abi_translate

open Context.Syntax

let run tenv fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let env = Lower_abi_common.init_env tenv fn in
    let* () = Params.lower env in
    let* () = Refs.canonicalize env in
    let* () = Rets.lower env in
    let* () = Calls.lower env in
    let* () = Vastart.lower env in
    let* () = Vaarg.lower env in
    let*? fn = Translate.go env in
    !!fn
  else
    Context.failf
      "In Lower_abi: expected SSA form for function $%s"
      (Func.name fn) ()
