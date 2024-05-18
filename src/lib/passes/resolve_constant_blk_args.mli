(** Runs a data-flow analysis to determine block arguments
    that are constant.

    The function must be in SSA form.
*)

open Core
open Virtual

val run : func -> func Or_error.t
