(** Removes assignments to variables that are never used.

    The function is assumed to be in SSA form.
*)

open Virtual

val run : func -> func
