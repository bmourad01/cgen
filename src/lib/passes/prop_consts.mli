(** Performs constant propagation and some simplifications to
    a function.

    The function is assumed to be in SSA form.
*)

open Core
open Virtual

val run : func -> func Context.t
