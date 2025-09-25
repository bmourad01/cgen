open Pseudo

(** Liveness analysis of a function. *)
module Live(M : Machine_intf.S_insn) : Live_intf.S
  with type var := M.Regvar.t
   and type var_comparator := M.Regvar.Set.Elt.comparator_witness
   and type func := (M.Insn.t, M.Reg.t) func
   and type blk := M.Insn.t blk
   and type cfg := Cfg.t

(** Removes instructions whose results are never used. *)
module Remove_dead_insns(M : Machine_intf.S_insn) : sig
  val run : (M.Insn.t, M.Reg.t) func -> (M.Insn.t, M.Reg.t) func
end

(** Emits the target-specific assembly code. *)
module Emit(M : Machine_intf.S) : sig
  val emit : Format.formatter -> (M.Insn.t, M.Reg.t) module_ -> unit
end
