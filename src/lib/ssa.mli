(** Utilities for maintaining SSA form. *)

(** Transforms the function into semi-pruned SSA form. *)
val run : Virtual.fn -> Virtual.fn Context.t
