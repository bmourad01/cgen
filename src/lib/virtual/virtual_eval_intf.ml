module Insn = Virtual_insn

module type S = sig
  (** [binop_int o x y] evaluates a binary operator [o] over integers
      [x] and [y], and returns the result if it is defined. *)
  val binop_int :
    Insn.binop ->
    Bv.t ->
    Bv.t ->
    [`bool of bool | `int of Bv.t * Type.imm] option

  (** [binop_single o x y] evaluates a binary operator [o] over 32-bit
      floats [x] and [y], and returns the result if it is defined. *)
  val binop_single :
    Insn.binop ->
    Float32.t ->
    Float32.t ->
    [`bool of bool | `float of Float32.t] option

  (** [binop_double o x y] evaluates a binary operator [o] over 64-bit
      floats [x] and [y], and returns the result if it is defined. *)
  val binop_double :
    Insn.binop ->
    float ->
    float ->
    [`bool of bool | `double of float] option

  (** [unop_int o x ty] evaluates a unary operator [o] over the integer
      [x] with type [ty], and returns the result if it is defined. *)
  val unop_int :
    Insn.unop ->
    Bv.t ->
    Type.imm ->
    [`double of float | `float of Float32.t | `int of Bv.t * Type.imm] option

  (** [unop_single o x] evaluates a unary operator [o] over the 32-bit float
      [x], and returns the result if it is defined. *)
  val unop_single :
    Insn.unop ->
    Float32.t ->
    [`double of float | `float of Float32.t | `int of Bv.t * Type.imm] option

  (** [unop_double o x] evaluates a unary operator [o] over the 64-bit float
      [x], and returns the result if it is defined. *)
  val unop_double :
    Insn.unop ->
    float ->
    [`double of float | `int of Bv.t * Type.imm] option
end
