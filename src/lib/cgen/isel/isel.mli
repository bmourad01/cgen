(** Instruction selection. *)

module Make(M : Machine_intf.S)(C : Context_intf.S) : sig
  (** Runs the instruction selection algorithm to produce a
      pseudo-assembly program. *)
  val run : Virtual.Abi.func -> (M.Insn.t, M.Reg.t) Pseudo.func C.t
end
