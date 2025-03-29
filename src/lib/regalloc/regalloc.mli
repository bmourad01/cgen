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

(** Computes the concrete stack layout, after register allocation. *)
module Layout_stack(M : Machine_intf.S)(C : Context_intf.S) : sig
  (** Computes the layout of the stack frame and replaces uses of
      [Virtual.Slot]s with their concrete offsets. *)
  val run : (M.Insn.t, M.Reg.t) func -> (M.Insn.t, M.Reg.t) func C.t
end
