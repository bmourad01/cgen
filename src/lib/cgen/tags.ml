(* Internal tags meant to maintain invariants. *)

open Core

(* SSA invariant. *)
let ssa = Dict.register "fn-ssa" (module Unit)

(* A division or remainder whose RHS is known to be nonzero. *)
let div_rem_nonzero = Dict.register "div-rem-nonzero" (module Unit)

(* Stack has been laid out. *)
let stack_laid_out = Dict.register "stack-laid-out" (module Unit)

let phi_var = Dict.register "phi-var"
    (module struct
      include Var.Set
      let pp ppf s =
        Format.fprintf ppf "(%a)"
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
             Var.pp)
          (Set.to_list s)
    end)

let needs_stack_frame = Dict.register "pseudo-fn-needs-stack-frame" (module Unit)
