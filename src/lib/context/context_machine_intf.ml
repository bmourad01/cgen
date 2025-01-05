(** The main interface for target machine implementations. *)

module type S = sig
  include Machine_intf.S

  (** A compilation context. *)
  type 'a context

  (** Lowers the ABI-specific details of a function for a given target. *)
  val lower_abi : Typecheck.env -> Virtual.func -> Virtual.Abi.func context
end
