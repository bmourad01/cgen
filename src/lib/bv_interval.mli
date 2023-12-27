(** Implements the abstract domain of fixed-size intervals
    over bitvectors. *)

(** An interval over the theory of bitvectors. *)
type t [@@deriving equal, sexp]

(** Creates an empty interval of [size] bits. *)
val create_empty : size:int -> t

(** Creates a full interval of [size] bits. *)
val create_full : size:int -> t

(** Creates an interval of [size] bits with a single [value]. *)
val create_single : value:Bv.t -> size:int -> t

(** Creates an interval of [size] bits with all negative numbers. *)
val create_negative : size:int -> t

(** The full interval of booleans. *)
val boolean_full : t

(** The interval for the boolean value [true]. *)
val boolean_true : t

(** The interval for the boolean value [false]. *)
val boolean_false : t

(** The interval for a single boolean value. *)
val boolean : bool -> t

(** The empty interval for booleans. *)
val boolean_empty : t

(** Creates an interval of [size] bits with a lower-bound [lo]
    and an upper bound [hi]. Note that the upper bound is
    exclusive.

    @raise Invalid_argument if the interval is empty ([lo = hi])
    and [lo] is not either the maximum unsigned value for [size]
    or zero.
*)
val create : lo:Bv.t -> hi:Bv.t -> size:int -> t

(** Similar to [create], but if [lo = hi] then falls back to
    [create_full]. *)
val create_non_empty : lo:Bv.t -> hi:Bv.t -> size:int -> t

(** The inclusive lower bound of the interval. *)
val lower : t -> Bv.t

(** The exclusive upper bound of the interval. *)
val upper : t -> Bv.t

(** The number of possible bits in the bitvector interval. *)
val size : t -> int

(** Returns [true] if the interval is empty. *)
val is_empty : t -> bool

(** Returns [true] if the interval is full. *)
val is_full : t -> bool

(** Returns [true] if the interval wraps around zero. *)
val is_wrapped : t -> bool

(** Returns [true] if [lower t > upper t] (unsigned). *)
val is_wrapped_hi : t -> bool

(** Returns [true] if the interval wraps around the smallest signed
    value. *)
val is_sign_wrapped : t -> bool

(** Returns [true] if [lower t > upper t] (signed). *)
val is_sign_wrapped_hi : t -> bool

(** Returns [Some v] if the interval consists of a single value [v],
    and [None] otherwise. *)
val single_of : t -> Bv.t option

(** Inverse of [single_of], where the interval contains all but one
    value. *)
val single_missing_of : t -> Bv.t option

(** Returns [true] if the interval consists of a single value. *)
val is_single : t -> bool

(** [is_strictly_smaller_than t1 t2] returns [true] if [t1] is strictly
    smaller than [t2].

    @raise Invalid_argument if [size t1 <> size t2]
*)
val is_strictly_smaller_than : t -> t -> bool

(** [is_larger_than t v] if the possible range of values in [t] is larger
    than [v]. *)
val is_larger_than : t -> Bv.t -> bool

(** Returns [true] if all the possible values are signed-less-than zero. *)
val is_all_negative : t -> bool

(** Opposite of [is_all_negative]. *)
val is_all_non_negative : t -> bool

(** The maximum unsigned value of the interval. *)
val unsigned_max : t -> Bv.t

(** The minimum unsigned value of the interval. *)
val unsigned_min : t -> Bv.t

(** The maximum signed value of the interval. *)
val signed_max : t -> Bv.t

(** The minimum signed value of the interval. *)
val signed_min : t -> Bv.t

(** Returns [true] if the interval contains a particular value. *)
val contains_value : t -> Bv.t -> bool

(** [contains t1 t2] returns [true] if all of the values in [t2]
    are contained in [t1]. *)
val contains : t -> t -> bool

(** Subtracts the upper and lower bounds by a given value. *)
val subtract : t -> Bv.t -> t

(** The preferred range for a given operation.

    [Smallest]: prefer the smallest range

    [Unsigned]: interpret as unsigned

    [Signed]: interpret as signed
*)
type preferred_range = Smallest | Unsigned | Signed

(** Returns the greatest lower bound.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val intersect : ?range:preferred_range -> t -> t -> t

(** Returns the least upper bound.

    @raise Invalid_argument if [size t1 <> size t2].
*)
val union : ?range:preferred_range -> t -> t -> t

(** Inverts the interval. *)
val inverse : t -> t

(** [difference t1 t2] is equivalent to [intersect t1 (inverse t2)]. *)
val difference : t -> t -> t

(** Zero-extend to a given [size].

    @raise Invalid_argument if [size t >= size].
*)
val zext : t -> size:int -> t

(** Sign-extend to a given [size].

    @raise Invalid_argument if [size t >= size].
*)
val sext : t -> size:int -> t

(** Truncate to a given [size].

    @raise Invalid_argument if [size t < size].
*)
val trunc : t -> size:int -> t

(** Addition.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val add : t -> t -> t

(** Subtraction.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val sub : t -> t -> t

(** Multiplication.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val mul : t -> t -> t

(** Signed max.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val smax : t -> t -> t

(** Unsigned max.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val umax : t -> t -> t

(** Signed min.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val smin : t -> t -> t

(** Unsigned min.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val umin : t -> t -> t

(** Unsigned division.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val udiv : t -> t -> t

(** Signed division.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val sdiv : t -> t -> t

(** Absolute value.

    If [int_min_is_poison] is [true], then operations on the minimum
    signed value for a given size is considered undefined. By default,
    it is [false].
*)
val abs : ?int_min_is_poison:bool -> t -> t

(** Unsigned remainder.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val urem : t -> t -> t

(** Signed remainder.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val srem : t -> t -> t

(** Logical NOT. *)
val lnot : t -> t

(** Negation. *)
val neg : t -> t

(** Logical AND.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val logand : t -> t -> t

(** Logical OR.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val logor : t -> t -> t

(** Logical XOR.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val logxor : t -> t -> t

(** Logical shift left.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val logical_shift_left : t -> t -> t

(** Logical shift right.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val logical_shift_right : t -> t -> t

(** Arithmetic shift right.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val arithmetic_shift_right : t -> t -> t

(** Extract from bits in the range [\[lo,hi\]].

    @raise Invalid_argument if [lo < 0] or [hi >= size t].
*)
val extract : t -> hi:int -> lo:int -> t

(** Concatenates two intervals. *)
val concat : t -> t -> t

(** [umulh t1 t2] extends [t1] and [t2] to double the amount of bits,
    multiplies them, and returns the range of the upper half.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val umulh : t -> t -> t

(** Same as [umulh], but interprets the result in terms of the signedness
    of both arguments.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val mulh : t -> t -> t

(** Rotate left.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val rotate_left : t -> t -> t

(** Rotate right.

    @raise Invalid_argument if [size t1 <> size t2]
*)
val rotate_right : t -> t -> t

(** Count leading zeros.

    if [zero_is_poison] is [true] and the interval contains zero, then
    the resulting range ignores the zero value. By default, it is [true].
*)
val clz : ?zero_is_poison:bool -> t -> t

(** Count trailing zeros.

    if [zero_is_poison] is [true] and the interval contains zero, then
    the resulting range ignores the zero value. By default, it is [true].
*)
val ctz : ?zero_is_poison:bool -> t -> t

(** Population count. *)
val popcnt : t -> t

(** A comparison predicate. *)
type predicate =
  | EQ | NE
  | LT | SLT
  | LE | SLE
  | GT | SGT
  | GE | SGE

(** [allowed_icmp_region t p] produces the smallest range [t'] such that
    it contains all values that may satisfy [p] in [t]. *)
val allowed_icmp_region : t -> predicate -> t

(** Pretty printing. *)
val pp : Format.formatter -> t -> unit

(** Pretty prints to a string. *)
val to_string : t -> string

module Infix : sig
  (** Infix of [add]. *)
  val (+) : t -> t -> t

  (** Infix of [sub]. *)
  val (-) : t -> t -> t

  (** Infix of [mul]. *)
  val ( * ) : t -> t -> t

  (** Infix of [udiv]. *)
  val (/) : t -> t -> t

  (** Infix of [sdiv]. *)
  val (/$) : t -> t -> t

  (** Infix of [urem]. *)
  val (%) : t -> t -> t

  (** Infix of [srem]. *)
  val (%^) : t -> t -> t

  (** Infix of [neg]. *)
  val (~-) : t -> t

  (** Infix of [logand]. *)
  val (land) : t -> t -> t

  (** Infix of [logor]. *)
  val (lor) : t -> t -> t

  (** Infix of [logxor]. *)
  val (lxor) : t -> t -> t

  (** Infix of [logical_shift_left]. *)
  val (lsl) : t -> t -> t

  (** Infix of [logical_shift_right]. *)
  val (lsr) : t -> t -> t

  (** Infix of [arithmetic_shift_right]. *)
  val (asr) : t -> t -> t
end
