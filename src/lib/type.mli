open Regular.Std

(** The base immediate types, which includes words [`i32]
    and longs [`i64]. *)
type imm_base = [
  | `i32
  | `i64
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a base immediate type. *)
val pp_imm_base : Format.formatter -> imm_base -> unit

(** All imediate types, which includes the base immediate types
    as well as bytes [`i8] and half-words [`i16]. *)
type imm = [
  | `i8
  | `i16
  | imm_base
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints an immediate type. *)
val pp_imm : Format.formatter -> imm -> unit

(** The floating point types, which includes single-precision
    [`f32] and double-precision [`f64] IEEE 754 numbers. *)
type fp = [
  | `f32
  | `f64
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a floating point type. *)
val pp_fp : Format.formatter -> fp -> unit

(** The basic (or primitive) types, which includes immediates
    and floating point numbers. *)
type basic = [
  | imm
  | fp
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a basic type. *)
val pp_basic : Format.formatter -> basic -> unit

(** A field of a compound type, which is either a basic type,
    or the [`name n] of another compound type, whose name is
    [n].

    A basic type [`elt (t, n)`] can specify how many instances
    [n] of the element occur in the field (akin to an inlined
    array of these elements). Note that [n <= 0] is illegal.
*)
type field = [
  | `elt  of basic * int
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a field. *)
val pp_field : Format.formatter -> field -> unit

(** A compound data type, consisting of a name, an optional
    alignment (in bytes), and a list of fields.

    An alignment [Some n] will indicate that the fields of the
    type are aligned by [n] bytes. Note that [n <= 0] is illegal.

    If no alignment is specified, then the fields of the type
    are aligned by the size of their largest member.
*)
type compound = [
  | `compound of string * int option * field list
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a compound type. *)
val pp_compound : Format.formatter -> compound -> unit

(** Special types that are not meant to be user-defined.

    [`mem] is the type of a memory. It is opaque and purely
    used for typing memory accesses and updates.

    [`flag] is the type of a condition flag. It is used for
    typing comparisons and conditional jumps.
*)
type special = [
  | `mem 
  | `flag
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a special type. *)
val pp_special : Format.formatter -> special -> unit

(** A type that is allowed to be used as a function argument.

    Note that return types also fall into this category.
*)
type arg = [
  | basic
  | compound
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty prints an argument type in the syntax that is allowed
    for function arguments. *)
val pp_arg : Format.formatter -> arg -> unit

(** A type. *)
type t = [
  | basic
  | compound
  | special
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a type. *)
val pp : Format.formatter -> t -> unit

include Regular.S with type t := t
