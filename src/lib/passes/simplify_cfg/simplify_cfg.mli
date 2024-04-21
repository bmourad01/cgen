(** Performs block merging, edge contraction, and other
    control-flow simplifications.

    The function must be in SSA form.
*)

open Virtual

val run : Typecheck.env -> func -> func Context.t
