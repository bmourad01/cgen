(** Performs block merging and edge contraction.

    The function must be in SSA form.
*)

open Core
open Virtual

val run : func -> func Or_error.t
