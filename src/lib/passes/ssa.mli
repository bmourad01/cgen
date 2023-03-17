(** Transforms a function into semi-pruned SSA form. *)

open Core
open Virtual

val run : Typecheck.env -> func -> func Or_error.t
