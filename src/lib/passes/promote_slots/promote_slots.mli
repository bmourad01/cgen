(** Attempts to promote uniform stack slots to SSA variables.

    Assumes the function is in SSA form.
*)

open Core
open Virtual

val run : func -> func Or_error.t
val run_abi : Abi.func -> Abi.func Or_error.t
