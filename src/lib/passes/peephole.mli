(** Performs constant propagation and some simplifications to
    a function.

    The function is assumed to be in SSA form.
*)

open Virtual

val run : Typecheck.env -> func -> func Context.t
