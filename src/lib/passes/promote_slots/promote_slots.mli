(** Attempts to promote uniform stack slots to SSA variables. *)

open Virtual

val run : func -> func Context.t
val run_abi : Abi.func -> Abi.func Context.t
