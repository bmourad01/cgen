(** The type system used by the virtual instruction set.

    It is designed for easy interop with the C ABI, and
    of course deriving and enforcing semantic properties
    of programs.
*)

open Regular.Std

(** The base immediate types, which includes words [`i32]
    and longs [`i64]. *)
type imm_base = [
  | `i32
  | `i64
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Size of [imm_base] in bits. *)
val sizeof_imm_base : imm_base -> int

(** Pretty-prints a base immediate type. *)
val pp_imm_base : Format.formatter -> imm_base -> unit

(** All imediate types, which includes the base immediate types
    as well as bytes [`i8] and half-words [`i16]. *)
type imm = [
  | `i8
  | `i16
  | imm_base
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Size of [imm] in bits. *)
val sizeof_imm : imm -> int

(** Pretty-prints an immediate type. *)
val pp_imm : Format.formatter -> imm -> unit

(** The floating point types, which includes single-precision
    [`f32] and double-precision [`f64] IEEE 754 numbers. *)
type fp = [
  | `f32
  | `f64
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Size of [fp] in bits. *)
val sizeof_fp : fp -> int

(** Pretty-prints a floating point type. *)
val pp_fp : Format.formatter -> fp -> unit

(** The basic (or primitive) types, which includes immediates
    and floating point numbers. *)
type basic = [
  | imm
  | fp
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Size of [basic] in bits. *)
val sizeof_basic : basic -> int

(** Pretty-prints a basic type. *)
val pp_basic : Format.formatter -> basic -> unit

(** A field of a compound type, which is either a basic type,
    or the [`name n] of another compound type, whose name is
    [n].

    A basic type [`elt (t, n)] can specify how many instances
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

(** An element of a compound data type's layout.

    [`elt t]: a field of type [t]

    [`pad n]: [n] bytes of padding
*)
type datum = [
  | `elt of basic
  | `pad of int
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a datum. *)
val pp_datum : Format.formatter -> datum -> unit

(** The layout of a compound data type.

    [align]: The data alignment, in bytes.

    [data]: The data layout, including padding.
*)
type layout = {
  align : int;
  data  : datum list;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** Returns the size of the layout in bits. *)
val sizeof_layout : layout -> int

(** Pretty-prints a layout. *)
val pp_layout : Format.formatter -> layout -> unit

(** [layout gamma c] derives the layout of the compound data
    type [c].

    A function [gamma] is provided to resolve the layout of
    fields [`name n], where [n] refers to another compound
    type.
*)
val layout : (string -> layout) -> compound -> layout

(** Pretty-prints a compound type (without the name). *)
val pp_compound : Format.formatter -> compound -> unit

(** Pretty-prints a compound type as a declaration. *)
val pp_compound_decl : Format.formatter -> compound -> unit

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
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty prints an argument type in the syntax that is allowed
    for function arguments. *)
val pp_arg : Format.formatter -> arg -> unit

(** A function prototype. *)
type proto = [
  | `proto of basic option * arg list * bool
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty prints a function prototype. *)
val pp_proto : Format.formatter -> proto -> unit

(** A type. *)
type t = [
  | basic
  | compound
  | special
] [@@deriving bin_io, compare, equal, hash, sexp]

include Regular.S with type t := t
