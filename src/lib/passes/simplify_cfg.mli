(** Performs block merging, edge contraction, and other
    control-flow simplifications.

    The function must be in SSA form.
*)

open Virtual

val run : func -> func Context.t
