module type S = sig
  type 'a context

  (** A machine register. *)
  type reg [@@deriving compare, equal, sexp]

  (** Pretty-prints a register. *)
  val pp_reg : Format.formatter -> reg -> unit

  (** Lowers the ABI-specific details of a function for a given target. *)
  val lower_abi : Typecheck.env -> Virtual.func -> Virtual.Abi.func context
end

