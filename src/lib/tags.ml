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

(* Stack has been laid out. *)
let stack_laid_out = Dict.register
    ~uuid:"dcb47c73-b6be-421a-875b-5cbbd857aab3"
    "stack-laid-out" (module Unit)

let phi_var = Dict.register
    ~uuid:"d4f9b426-c84a-47a6-827d-5de610f00cbe" "phi-var"
    (module struct
      include Var.Set
      let pp ppf s =
        Format.fprintf ppf "(%a)"
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
             Var.pp)
          (Set.to_list s)
    end)
