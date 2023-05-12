(** A representation of Virtual instructions as an expression tree.

    Given a sequence of instructions, a maximal DAG is formed according
    to control and data flow throughout a function.

    The motivation for this data representation is to allow for easy
    pattern matching across (and within) basic blocks. Uses may include
    performing certain optimizations, instruction selection, and so on.
*)

open Core
open Virtual

(** A subexpression used to compute the result of an instruction. *)
type pure =
  | Palloc  of Label.t * int
  | Pbinop  of Label.t * Insn.binop * pure * pure
  | Pcall   of Label.t * Type.basic * global * pure list * pure list
  | Pdouble of float
  | Pint    of Bitvec.t * Type.imm
  | Pload   of Label.t * Type.basic * pure
  | Psel    of Label.t * Type.basic * pure * pure * pure
  | Psingle of Float32.t
  | Psym    of string * int
  | Punop   of Label.t * Insn.unop * pure
  | Pvar    of Var.t
[@@deriving bin_io, compare, equal, sexp]

(** A global control-flow destination. *)
and global =
  | Gaddr of Bitvec.t
  | Gpure of pure
  | Gsym  of string
[@@deriving bin_io, compare, equal, sexp]

(** A local control-flow destination. *)
and local = Label.t * pure list
[@@deriving bin_io, compare, equal, sexp]

(** A control-flow destination. *)
and dst =
  | Dglobal of global
  | Dlocal  of local
[@@deriving bin_io, compare, equal, sexp]

(** Pretty-prints a subexpression. *)
val pp_pure : Format.formatter -> pure -> unit

(** Pretty-prints a global control-flow destination. *)
val pp_global : Format.formatter -> global -> unit

(** Pretty-prints a local control-flow destination. *)
val pp_local : Format.formatter -> local -> unit

(** Pretty-prints a control-flow destination. *)
val pp_dst : Format.formatter -> dst -> unit

(** A switch table. *)
type table = (Bitvec.t * local) list
[@@deriving bin_io, compare, equal, sexp]

(** Pretty-prints a switch table. *)
val pp_table : Format.formatter -> table -> unit

(** An expression. *)
type t =
  | Ebr    of pure * dst * dst
  | Ecall  of global * pure list * pure list
  | Ejmp   of dst
  | Eret   of pure
  | Eset   of Var.t * pure
  | Estore of Type.basic * pure * pure
  | Esw    of Type.imm * pure * local * table
[@@deriving bin_io, compare, equal, sexp]

(** Pretty-prints an expression. *)
val pp : Format.formatter -> t -> unit

(** [build fn l] attempts to construct an expression based on
    the label [l] in function [fn].

    [l] must refer to either a block, in which case the expression
    is built starting from the control instruction, or a regular
    data instruction.

    The algorithm walks backwards and constructs a maximal dag,
    substituting in subexpressions for variables when possible.

    [fn] is assumed to be in SSA form. If [fn] is not well-formed
    or [l] doesn't exist, an error is returned.

    If the control/data instruction referred to by [l] is not
    expressible, then [Ok None] is returned.
*)
val build : func -> Label.t -> t option Or_error.t
