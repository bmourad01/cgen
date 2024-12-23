(** Instruction selection. *)

module Make(M : Context.Machine) : sig
  val run : Virtual.Abi.func -> M.Insn.t Pseudo.func Context.t
end
