(* Internal tags meant to maintain invariants. *)

open Core

(* SSA invariant. *)
let ssa = Dict.register
    ~uuid:"fe85f122-1f49-4248-bdd1-970f4856c419"
    "fn-ssa" (module Unit)

(* A division or remainder whose RHS is known to be nonzero. *)
let div_rem_nonzero = Dict.register
    ~uuid:"63453523-dbfd-4bda-b93c-ac47e1a98ee9"
    "div-rem-nonzero" (module Unit)
