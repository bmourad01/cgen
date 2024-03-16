open Core

(** The base set of operations in an instruction. *)
module type S = sig
  type operand

  (** Arithmetic binary operations.

      [`add t]: addition.

      [`div t]: division.

      [`mul t]: multiplication.

      [`mulh t]: signed immediate high multiplication.

      [`rem t]: remainder.

      [`sub t]: subtraction.

      [`udiv t]: unsigned division (immediate only).

      [`umulh t]: unsigned immediate high multiplication.

      [`urem t]: unsigned remainder (immediate only).
  *)
  type arith_binop = [
    | `add   of Type.basic
    | `div   of Type.basic
    | `mul   of Type.basic
    | `mulh  of Type.imm
    | `rem   of Type.basic
    | `sub   of Type.basic
    | `udiv  of Type.imm
    | `umulh of Type.imm
    | `urem  of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the arithmetic binary operator. *)
  val pp_arith_binop : Format.formatter -> arith_binop -> unit

  (** Arithmetic unary operations.

      [`neg t]: negation.
  *)
  type arith_unop = [
    | `neg of Type.basic
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the arithmetic unary operator. *)
  val pp_arith_unop : Format.formatter -> arith_unop -> unit

  (** Bitwise binary operations.

      [`and_ t]: bitwise intersection (AND).

      [`or_ t]: bitwise union (OR).

      [`asr_ t]: arithmetic shift right.

      [`lsl_ t]: logical shift left.

      [`lsr_ t]: logical shift right.

      [`rol t]: rotate left.

      [`ror t]: rotate right.

      [`xor t]: bitwise difference (exclusive-OR).
  *)
  type bitwise_binop = [
    | `and_ of Type.imm
    | `or_  of Type.imm
    | `asr_ of Type.imm
    | `lsl_ of Type.imm
    | `lsr_ of Type.imm
    | `rol  of Type.imm
    | `ror  of Type.imm
    | `xor  of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the bitwise binary operator. *)
  val pp_bitwise_binop : Format.formatter -> bitwise_binop -> unit

  (** Bitwise unary operations.

      [`clz t]: count leading zeroes.

      [`ctz t]: count trailing zeroes.

      [`not_ t]: bitwise complement (NOT).

      [`popcnt t]: population count (number of set bits).
  *)
  type bitwise_unop = [
    | `clz    of Type.imm
    | `ctz    of Type.imm
    | `not_   of Type.imm
    | `popcnt of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the bitwise unary operator. *)
  val pp_bitwise_unop : Format.formatter -> bitwise_unop -> unit

  (** Comparison operations.

      [`eq t l, r)]: equal.

      [`ge t]: greater or equal.

      [`gt t]: greater than.

      [`le t]: less or equal.

      [`lt t]: less than.

      [`ne t]: not equal.

      [`o t]: ordered (floating point only).

      [`sge t]: signed greater or equal (immediate only).

      [`sgt t]: signed greater than (immediate only).

      [`sle t]: signed less or equal (immediate only).

      [`slt t]: signed less than (immediate only).

      [`uo t]: unordered (floating point only).
  *)
  type cmp = [
    | `eq  of Type.basic
    | `ge  of Type.basic
    | `gt  of Type.basic
    | `le  of Type.basic
    | `lt  of Type.basic
    | `ne  of Type.basic
    | `o   of Type.fp
    | `sge of Type.imm
    | `sgt of Type.imm
    | `sle of Type.imm
    | `slt of Type.imm
    | `uo  of Type.fp
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints a comparison operation. *)
  val pp_cmp : Format.formatter -> cmp -> unit

  (** Cast operations.

      [`fext t]: extends a floating point value to a higher
      precision.

      [`fibits t]: reinterpret the bits of an integer as a
      float of type [t].

      [`flag t]: converts a flag bit into an integer of type [t].

      [`ftosi (t, i)]: cast a float of type [t] to a signed
      integer of type [i].

      [`ftoui (t, i)]: cast a float of type [t] to an unsigned
      integer of type [i].

      [`ftrunc t]: truncate a float to a float of type [t].

      [`ifbits t]: reinterpret the bits of a floating point
      number as an integer of type [t].

      [`itrunc t]: truncate an integer to an integer of type [t].

      [`sext t]: sign-extend an integer to an integer of type [t].

      [`sitof (t, f)]: cast a signed integer of type [t] to a float
      of type [f].

      [`uitof (t, f)]: cast an unsigned integer of type [t] to a
      float of type [f].

      [`zext t]: zero-extend an integer to an integer of type [t].
  *)
  type cast = [
    | `fext   of Type.fp
    | `fibits of Type.fp
    | `flag   of Type.imm
    | `ftosi  of Type.fp * Type.imm
    | `ftoui  of Type.fp * Type.imm
    | `ftrunc of Type.fp
    | `ifbits of Type.imm_base
    | `itrunc of Type.imm
    | `sext   of Type.imm
    | `sitof  of Type.imm * Type.fp
    | `uitof  of Type.imm * Type.fp
    | `zext   of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints a cast operation. *)
  val pp_cast : Format.formatter -> cast -> unit

  (** Copy operations.

      [`copy t]: move to a destination of type [t].
  *)
  type copy = [
    | `copy  of Type.basic
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints a copy operation. *)
  val pp_copy : Format.formatter -> copy -> unit

  (** All binary operations. *)
  type binop = [
    | arith_binop
    | bitwise_binop
    | cmp
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the binary operator. *)
  val pp_binop : Format.formatter -> binop -> unit

  (** All unary operations. *)
  type unop = [
    | arith_unop
    | bitwise_unop
    | cast
    | copy
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the unary operator. *)
  val pp_unop : Format.formatter -> unop -> unit

  (** All basic instructions.

      [`bop (x, b, l, r)]: compute [b(l, r)] and store the result in [x].

      [`uop (x, u, a)]: compute [u(a)] and store the result in [x].

      [`sel (x, t, c, l, r)]: evaluate [c]; if non-zero then select [l]
      and assign to [x], otherwise select [r]. Both [l] and [r] must have
      type [t].
  *)
  type basic = [
    | `bop of Var.t * binop * operand * operand
    | `uop of Var.t * unop * operand
    | `sel of Var.t * Type.basic * Var.t * operand * operand
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the basic instruction. *)
  val free_vars_of_basic : basic -> Var.Set.t

  (** Pretty-prints a basic instruction. *)
  val pp_basic : Format.formatter -> basic -> unit

  (** Memory operations.

      [`load (x, t, a)]: load a value of type [t] from address [a] and
      assign the result to [x].

      [`store (t, v, a)]: store a value [v] of type [t] to address [a].
  *)
  type mem = [
    | `load  of Var.t * Type.basic * operand
    | `store of Type.basic * operand * operand
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the memory operation. *)
  val free_vars_of_mem : mem -> Var.Set.t

  (** Pretty-prints a memory operation. *)
  val pp_mem : Format.formatter -> mem -> unit
end
