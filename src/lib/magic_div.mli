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

    @raise Invalid_argument if [d] is [0] or [1].
*)
val unsigned : Bv.t -> Type.imm -> Bv.t * bool * int

(** [signed d t] computes the magic constant for signed
    division/remainder for the divisor [d] of type [t].

    Returns a pair of the constant and the number of bits to shift
    right.

    @raise Invalid_argument if [d] is [-1], [0], or [1].
*)
val signed : Bv.t -> Type.imm -> Bv.t * int
