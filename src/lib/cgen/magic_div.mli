(** Implementation of an algorithm to compute the "magic" constants when
    dividing or taking the remainder of an integer by a fixed constant.

    This is used in the technique of strength reduction, where we can
    replace this division/remainder by a constant with a series of cheaper
    arithmetic and shift instructions.
*)

(** [unsigned d t] computes the magic constant for unsigned
    division/remainder for the divisor [d] of type [t].

    Returns a triple of the constant, a boolean indicating whether
    an additional [add] instruction is needed, and the number of bits
    to shift right.

    Raises [Invalid_argument] if [d] is [0] or [1].
*)
val unsigned : Bv.t -> Type.imm -> Bv.t * bool * int

(** [signed d t] computes the magic constant for signed
    division/remainder for the divisor [d] of type [t].

    Returns a pair of the constant and the number of bits to shift
    right.

    Raises [Invalid_argument] if [d] is [-1], [0], or [1].
*)
val signed : Bv.t -> Type.imm -> Bv.t * int

(** [mulinv a t] is the multiplicative inverse of the odd value [a] modulo
    [2^W], where [W] is the bit-width of [t] (i.e. [a * mulinv a t = 1]
    modulo [2^W]).

    The result is unspecified if [a] is even.
*)
val mulinv : Bv.t -> Type.imm -> Bv.t

(** The shape of a divisibility test [(x mod d) = 0] for a constant divisor
    [d], used to strength-reduce [(x % d) == 0] or [(x % d) != 0] away from
    a full remainder.

    - [Pow2_mask m]: [d] is (in magnitude) a power of two; the test is
      [(x land m) = 0].
    - [Test {factor; bias; rot; limit}]: the test is
      [ror ((x * factor) + bias) rot <= limit], with an {e unsigned}
      comparison. For unsigned divisors, [bias] is zero. The signed test
      folds in a bias so that a single unsigned comparison suffices.
*)
type divisible =
  | Pow2_mask of Bv.t
  | Test of {
      factor : Bv.t;
      bias   : Bv.t;
      rot    : int;
      limit  : Bv.t;
    }

(** [divisible ~signed d t] computes the parameters of the divisibility
    test [(x mod d) = 0], where [x] has type [t] and [d] is the constant
    divisor (interpreted as signed when [signed] is [true]).

    pre: [d] is not [0] or [1]; when [signed], [d] is also not [-1].
*)
val divisible : signed:bool -> Bv.t -> Type.imm -> divisible
