open Virtual

module Make(M : Context.Machine)(C : Context_intf.S) = struct
  (* open C.Syntax *)
  
  let run fn =
    if Dict.mem (Abi.Func.dict fn) Tags.ssa then
      C.failf "Select_insns: not implemented" ()
    else
      C.failf
        "In Select_insns: expected SSA form for function $%s"
        (Abi.Func.name fn) ()
end
