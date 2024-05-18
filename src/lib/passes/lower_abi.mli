(** This pass lowers a Virtual function into a Virtual ABI function,
    where parameter passing, compound types, and platform-specific
    constructs in Virtual are desugared and made to comform to a
    specific ABI.

    The function is assumed to be in SSA form, and the transformed
    function is expected to preserve it, modulo the presence of
    explicit registers.
*)

val run : Typecheck.env -> Virtual.func -> Virtual.Abi.func Context.t
