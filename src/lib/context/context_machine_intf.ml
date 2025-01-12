(** The main interface for target machine implementations. *)

module type S = sig
  include Machine_intf.S

  (** A compilation context. *)
  type 'a context

  (** Lowers the ABI-specific details of a function for a given target.

      The function is expected to be in SSA form.

      The resulting output is expected to preserve the function's [dict],
      specifically information about linkage and whether the function is
      variadic or not.
  *)
  val lower_abi : Typecheck.env -> Virtual.func -> Virtual.Abi.func context
end
