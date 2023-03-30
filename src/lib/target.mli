(** A compilation target. *)

open Regular.Std

(** Registers belonging to a target. *)
module Reg : sig
  (** Register classes.

      [flag]: a flag register.

      [fp]: a floating-point register.

      [gpr]: a general-purpose register.

      [sp]: a stack pointer register.
  *)
  type cls = [
    | `flag
    | `fp
    | `gpr
    | `sp
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  type t

  (** Creates a register.

      [name]: the name of the register.

      [width]: the size of the register in bits.

      [cls]: the register class.
  *)
  val create :
    name:string ->
    width:int ->
    cls:cls ->
    t

  (** The name of the register. *)
  val name : t -> string

  (** The size of the register in bits. *)
  val width : t -> int

  (** The register class. *)
  val cls : t -> cls

  (** [is_cls r cls] returns [true] if [r] has belongs to [cls]. *)
  val is_cls : t -> cls -> bool

  (** Helper for 1-bit registers. *)
  val r1 : name:string -> cls:cls -> t

  (** Helper for 8-bit registers. *)
  val r8 : name:string -> cls:cls -> t

  (** Helper for 16-bit registers. *)
  val r16 : name:string -> cls:cls -> t

  (** Helper for 32-bit registers. *)
  val r32 : name:string -> cls:cls -> t

  (** Helper for 64-bit registers. *)
  val r64 : name:string -> cls:cls -> t

  (** Helper for 128-bit registers. *)
  val r128 : name:string -> cls:cls -> t

  include Regular.S with type t := t
end

type reg = Reg.t [@@deriving bin_io, compare, equal, hash, sexp]

type t

(** Creates a target.

    [flag]: flag registers.

    [fp]: floating-point registers.

    [gpr]: general-purpose registers.

    [name]: the name of the target.

    [word]: the type for the word size of the target.

    [little]: if [true], the target is little-endian.

    [sp]: stack pointer register.
*)
val create :
  ?flag:reg list ->
  ?fp:reg list ->
  ?gpr:reg list ->
  name:string ->
  word:Type.imm_base ->
  little:bool ->
  sp:reg ->
  unit ->
  t

(** The name of the target. *)
val name : t -> string

(** The type of the native word size of the target. *)
val word : t -> Type.imm_base

(** The native bit-width of the target. *)
val bits : t -> int

(** Returns [true] if the target is little-endian. *)
val little : t -> bool

(** Returns the set of flag registers. *)
val flag : t -> Reg.Set.t

(** Returns the set of floating-point registers. *)
val fp : t -> Reg.Set.t

(** Returns the set of general-purpose registers. *)
val gpr : t -> Reg.Set.t

(** Returns the stack pointer register. *)
val sp : t -> reg

include Regular.S with type t := t
