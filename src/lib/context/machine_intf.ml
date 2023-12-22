module type S = sig
  type 'a context

  (** A machine register. *)
  module Reg : sig
    type t [@@deriving compare, equal, sexp]
    val pp : Format.formatter -> t -> unit
  end

  (** Lowers the ABI-specific details of a function for a given target. *)
  val lower_abi : Typecheck.env -> Virtual.func -> Virtual.Abi.func context
end

