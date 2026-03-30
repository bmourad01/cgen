(** Register allocation *)

open Pseudo

(** The Iterated Register Coalescing algorithm. *)
module IRC(M : Machine_intf.S)(C : Context_intf.S) : sig
  (** Performs register allocation on the function.

      [max_rounds] provides the maximum number of iterations that
      the algorithm will perform in order to find a solution.

      [invariants] enables internal invariant checking on every iteration
      of the main worklist loop. This is expensive and intended for
      development and testing; it defaults to [false].
  *)
  val run :
    ?max_rounds:int ->
    ?invariants:bool ->
    (M.Insn.t, M.Reg.t) func ->
    (M.Insn.t, M.Reg.t) func C.t
end
