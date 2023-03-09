(** Utilities for maintaining SSA form. *)

(** Transforms the function into semi-pruned SSA form. *)
val run : Virtual.func -> Virtual.func Core.Or_error.t
