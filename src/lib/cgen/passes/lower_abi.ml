open Virtual
open Context.Syntax

let run ?(invariants = false) tenv fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let* (module Machine) = Context.machine in
    let module Lower = Machine.Lower_abi(Context) in
    let* fn = Lower.run tenv fn in
    (* The SSA tag must be set unconditionally, since the downstream ABI
       passes require it. When `invariants` is disabled we trust that
       `Lower.run` preserved SSA form rather than paying to re-verify it. *)
    let+? () = if invariants then Ssa.check_abi fn else Ok () in
    Abi.Func.with_tag fn Tags.ssa ()
  else
    Context.failf
      "In Lower_abi: expected SSA form for function $%s"
      (Func.name fn) ()
