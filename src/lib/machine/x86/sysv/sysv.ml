module Make(Context : Context_intf.S_virtual) = struct
  open Context.Syntax

  module Params = Sysv_params.Make(Context)
  module Refs = Sysv_refs.Make(Context)
  module Rets = Sysv_rets.Make(Context)
  module Calls = Sysv_calls.Make(Context)
  module Vastart = Sysv_vastart.Make(Context)
  module Vaarg = Sysv_vaarg.Make(Context)
  module Translate = Sysv_translate.Make(Context)

  let run tenv fn =
    let env = Sysv_common.init_env tenv fn in
    let* () = Params.lower env in
    let* () = Refs.lower env in
    let* () = Rets.lower env in
    let* () = Calls.lower env in
    let* () = Vastart.lower env in
    let* () = Vaarg.lower env in
    let* fn = Translate.go env in
    !!fn
end
