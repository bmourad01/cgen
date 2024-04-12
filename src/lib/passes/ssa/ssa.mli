(** Transforms a function into semi-pruned SSA form. *)

open Core
open Virtual

val run : func -> func Or_error.t

(** Verify that the function satisfies the invariants
    of SSA form. *)
val check : func -> unit Or_error.t
