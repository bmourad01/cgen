(** This pass lowers a Virtual function into a Virtual ABI
    function, where parameter passing is desugared and made
    to comform to a specific ABI.

    The function is assumed to be in SSA form.
*)

open Virtual

val run : Typecheck.env -> func -> Abi.func Context.t
