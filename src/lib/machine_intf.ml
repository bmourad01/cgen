(** The main interface for target machine implementations. *)

open Core

module type S = sig
  (** The target descriptor. *)
  val target : Target.t

  (** A machine register. *)
  module Reg : sig
    type t [@@deriving bin_io, compare, equal, sexp]

    (** The type of the register. *)
    val typeof : t -> [Type.basic | `v128]

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

  (** A machine register or a virtual variable.

      To ease implementation of the backend, instructions can refer to
      both registers and variables after instruction selection. After
      register allocation, it is expected that no variables will be
      present.
  *)
  module Regvar : sig
    type t [@@deriving bin_io, compare, equal, sexp]

    val reg : Reg.t -> t
    val var : Var.t -> t
    val is_reg : t -> bool
    val is_var : t -> bool
    val which : t -> (Reg.t, Var.t) Either.t
    val pp : Format.formatter -> t -> unit

    include Comparator.S with type t := t
    module Set : Set_intf.S with type Elt.t = t
  end

  (** A machine instruction. *)
  module Insn : sig
    (** The abstract representation of an instruction. *)
    type t [@@deriving bin_io, compare, equal, sexp]

    (** The set of arguments that the instruction reads from. *)
    val reads : t -> Regvar.Set.t

    (** The set of arguments that the instruction writes to. *)
    val writes : t -> Regvar.Set.t

    (** Pretty-prints the instruction. *)
    val pp : Format.formatter -> t -> unit
  end

  (** Instruction selection. *)
  module Isel(C : Context_intf.S) : sig
    (** Rewrite rules for instruction selection. *)
    val rules : (Regvar.t, Insn.t) Isel_rewrite.Rule(C).t list
  end
end
