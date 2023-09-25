(** Attempts to transform normal call instructions into
    tail calls. *)

open Virtual

val run : func -> func
