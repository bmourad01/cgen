(** Instruction selection. *)

module Make(M : Context.Machine)(C : Context_intf.S) : sig
  val run : Virtual.Abi.func -> M.Insn.t Pseudo.func C.t
end
