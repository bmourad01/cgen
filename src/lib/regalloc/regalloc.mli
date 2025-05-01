(** Register allocation *)

open Pseudo

(** The Iterated Register Coalescing algorithm. *)
module IRC(M : Machine_intf.S)(C : Context_intf.S) : sig
  (** Performs register allocation on the function.

      [max_rounds] provides the maximum number of iterations that
      the algorithm will perform in order to find a solution.
  *)
  val run : ?max_rounds:int -> (M.Insn.t, M.Reg.t) func -> (M.Insn.t, M.Reg.t) func C.t
end
