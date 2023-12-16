open Context.Syntax

let run tenv fn =
  let env = Sysv_common.init_env tenv fn in
  let* () = Sysv_params.lower env in
  let* () = Sysv_refs.canonicalize env in
  let* () = Sysv_rets.lower env in
  let* () = Sysv_calls.lower env in
  let* () = Sysv_vastart.lower env in
  let* () = Sysv_vaarg.lower env in
  let*? fn = Sysv_translate.go env in
  !!fn
