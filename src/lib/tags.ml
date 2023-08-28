(* Internal tags meant to maintain invariants. *)

open Core

(* SSA invariant. *)
let ssa = Dict.register
    ~uuid:"fe85f122-1f49-4248-bdd1-970f4856c419"
    "fn-ssa" (module Unit)
