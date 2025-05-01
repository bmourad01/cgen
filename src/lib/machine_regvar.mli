(** A register or variable that may be mentioned in a [Machine]
    instruction. *)

open Core
open Regular.Std

(** A register class.

    [GPR]: general-purpose register

    [FP]: floating-point register
*)
type cls = GPR | FP [@@deriving bin_io, compare, equal, hash, sexp]

val pp_cls : Format.formatter -> cls -> unit

(** A machine register or a virtual variable.

    To ease implementation of the backend, instructions can refer to
    both registers and variables after instruction selection. After
    register allocation, it is expected that no variables will be
    present.
*)
module type S = sig
  type t
  type reg

  (** Construct a register. *)
  val reg : reg -> t

  (** Construct a variable, with the provided register class. *)
  val var : cls -> Var.t -> t

  (** Returns [true] if it is a register. *)
  val is_reg : t -> bool

  (** Returns [true] if it is a variable. *)
  val is_var : t -> bool

  (** Returns the discrimination. *)
  val which : t -> (reg, Var.t * cls) Either.t

  include Regular.S with type t := t
end

(** Required interface for the register type. *)
module type Reg = sig
  type t [@@deriving bin_io, compare, equal, hash, sexp]
  val pp : Format.formatter -> t -> unit
end

(** The name of the module, for the [Regular] instance. *)
module type Name = sig
  val module_name : string
end

(** Helper for making the boilerplate stuff for [Regvar]
    as required by the [Machine_intf.S] signature. *)
module Make(R : Reg)(_ : Name) : S with type reg := R.t
