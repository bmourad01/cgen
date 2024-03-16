(** Removes assignments to variables that are never used.

    The function is assumed to be in SSA form.
*)

open Core
open Virtual

val run : func -> func Or_error.t
val run_abi : Abi.func -> Abi.func Or_error.t
