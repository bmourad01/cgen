(** Transforms a function into semi-pruned SSA form. *)

open Core
open Virtual

val run : func -> func Or_error.t
