(** Runs a data-flow analysis to determine block arguments that are constant.

    The function is assumed to be in SSA form.
*)

open Virtual

val run : func -> func
