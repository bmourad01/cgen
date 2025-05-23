(** Single-precision floating-point numbers.

    This is here because the OCaml compiler only supports double-precision
    floating point numbers. We rely on the C behavior of [float] types on
    the native machine, and we implement the minimal subset of operations
    to support those seen in the Virtual IR.
*)

open Core

type t [@@deriving bin_io, sexp]

(** Convert from a double-precistion float. *)
val of_float : float -> t

(** Convert to a double-precision float. *)
val to_float : t -> float

(** Returns [true] if the number is zero. *)
val is_zero : t -> bool

(** Returns [true] if the number is an infinity. *)
val is_inf : t -> bool

(** Returns [true] if the number is negative. *)
val is_negative : t -> bool

(** Returns [true] if the number is "Not a Number". *)
val is_nan : t -> bool

(** Addition. *)
val add : t -> t -> t

(** Division. *)
val div : t -> t -> t

(** Multiplication. *)
val mul : t -> t -> t

(** Negation. *)
val neg : t -> t

(** Subtraction. *)
val sub : t -> t -> t

(** Addition *)
val (+) : t -> t -> t

(** Division. *)
val (/) : t -> t -> t

(** Multiplication. *)
val ( * ) : t -> t -> t

(** Negation. *)
val (-~) : t -> t

(** Subtraction. *)
val (-) : t -> t -> t

(** Returns the underlying bits of the number. *)
val bits : t -> int32

(** Converts the underlying bits to a number. *)
val of_bits : int32 -> t

(** Convert to an 8-bit signed integer. *)
val to_int8 : t -> int

(** Convert to a 16-bit signed integer. *)
val to_int16 : t -> int

(** Convert to a 32-bit signed integer. *)
val to_int32 : t -> int32

(** Convert to a 64-bit signed integer. *)
val to_int64 : t -> int64

(** Convert from an 8-bit unsigned integer. *)
val to_uint8 : t -> int

(** Convert to a 16-bit unsigned integer. *)
val to_uint16 : t -> int

(** Convert to a 32-bit unsigned integer. *)
val to_uint32 : t -> int32

(** Convert to a 64-bit unsigned integer. *)
val to_uint64 : t -> int64

(** Convert from an 8-bit signed integer. *)
val of_int8 : int -> t

(** Convert from a 16-bit signed integer. *)
val of_int16 : int -> t

(** Convert from a 32-bit signed integer. *)
val of_int32 : int32 -> t

(** Convert from a 64-bit signed integer. *)
val of_int64 : int64 -> t

(** Convert from an 8-bit unsigned integer. *)
val of_uint8 : int -> t

(** Convert from a 16-bit unsigned integer. *)
val of_uint16 : int -> t

(** Convert from a 32-bit unsigned integer. *)
val of_uint32 : int32 -> t

(** Convert from a 64-bit unsigned integer. *)
val of_uint64 : int64 -> t

(** Convert to a string representation. *)
val to_string : t -> string

(** Convert from a string representation. *)
val of_string : string -> t

(** Returns [true] if both numbers are equal. *)
val equal : t -> t -> bool

(** [compare x y] returns [0] if [x = y], a negative number if [x < y],
    and a positive number if [x > y].

    Like [Float.compare], the NaN case is treated as equal to itself
    and less than any other value, which ensures a total ordering.
*)
val compare : t -> t -> int

val (=) : t -> t -> bool
val (<>) : t -> t -> bool
val (>=) : t -> t -> bool
val (>) : t -> t -> bool
val (<=) : t -> t -> bool
val (<) : t -> t -> bool

(** [is_ordered x y] returns [true] if the comparison between [x] and [y]
    is ordered. *)
val is_ordered : t -> t -> bool

(** [is_unordered x y] returns [true] if the comparison between [x] and [y]
    is unordered. *)
val is_unordered : t -> t -> bool

val hash : t -> int
val hash_fold_t : Hash.state -> t -> Hash.state
