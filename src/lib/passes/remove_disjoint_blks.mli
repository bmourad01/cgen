(** Removes all the blocks from a function that are unreachable
    from the entry block. *)

open Virtual

val run : func -> func
val run_abi : Abi.func -> Abi.func
