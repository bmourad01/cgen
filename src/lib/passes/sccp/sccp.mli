(** Performs the classic Sparse Conditional Constant
    Propagation (SCCP) pass.

    The function is assumed to be in SSA form.
*)

open Core
open Virtual

val run : Typecheck.env -> func -> func Or_error.t
