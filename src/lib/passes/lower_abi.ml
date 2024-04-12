open Virtual
open Context.Syntax

let run tenv fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let* (module Machine) = Context.machine in
    let* fn = Machine.lower_abi tenv fn in
    let*? () = Ssa.check_abi fn in
    !!(Abi.Func.with_tag fn Tags.ssa ())
  else
    Context.failf
      "In Lower_abi: expected SSA form for function $%s"
      (Func.name fn) ()
