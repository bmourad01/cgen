open Virtual
open Context.Syntax

let run tenv fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let* (module Machine) = Context.machine in
    Machine.lower_abi tenv fn
  else
    Context.failf
      "In Lower_abi: expected SSA form for function $%s"
      (Func.name fn) ()
