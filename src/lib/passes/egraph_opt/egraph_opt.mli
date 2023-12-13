(** Uses the [Egraph] module to perform a variety of optimizations
    to a function.

    The function is assumed to be in SSA form.
*)

open Virtual

val run : Typecheck.env -> func -> func Context.t
