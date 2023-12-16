(** This pass lowers a Virtual function into a Virtual ABI
    function, where parameter passing is desugared and made
    to comform to a specific ABI.

    The function is assumed to be in SSA form.
*)

val run : Typecheck.env -> Virtual.func -> Virtual.Abi.func Context.t
