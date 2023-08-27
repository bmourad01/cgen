(** Uses the [Egraph] module to perform a variety of optimizations
    to a function.

    This actually turns out to be more than a typical "peephole"
    optimizer, but we will stick with that name for this pass,
    because it sounds nice.

    The function is assumed to be in SSA form.
*)

open Virtual

val run : Typecheck.env -> func -> func Context.t
