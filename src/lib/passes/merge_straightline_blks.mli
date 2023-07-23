(** Merges blocks that are separated by only a single unconditional edge.

    The function must be in SSA form.
*)

open Virtual

val run : func -> func
