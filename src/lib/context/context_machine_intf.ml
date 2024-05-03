module type S = sig
  type 'a context

  (** A machine register. *)
  module Reg : sig
    type t [@@deriving compare, equal, sexp]

    (** Pretty-print the register name. *)
    val pp : Format.formatter -> t -> unit

    (** Decode the register from a string.

        @raise Invalid_argument if the string is not a valid register name.
    *)
    val of_string_exn : string -> t

    (** Same as [of_string_exn], but returns [None] if the string is not a
        valid register name. *)
    val of_string : string -> t option
  end

  (** A machine instruction. *)
  module Insn : sig
    type 'a t [@@deriving compare, equal, sexp]
  end

  (** Lowers the ABI-specific details of a function for a given target. *)
  val lower_abi : Typecheck.env -> Virtual.func -> Virtual.Abi.func context
end

