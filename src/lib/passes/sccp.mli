(** Uses the [Intervals] analysis to perform the classic
    Sparse Conditional Constant Propagation (SCCP) pass. *)

open Core
open Virtual

val run : Typecheck.env -> func -> func Or_error.t
