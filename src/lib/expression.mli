(** A representation of Virtual instructions as an expression tree.

    Given a sequence of instructions, a maximal DAG is formed according
    to control and data flow throughout a function.

    The motivation for this data representation is to allow for easy
    pattern matching across (and within) basic blocks. Uses may include
    performing certain optimizations, instruction selection, and so on.
*)

open Virtual

(** A subexpression used to compute the result of an instruction. *)
type pure =
  | Palloc  of Label.t * int
  | Pbinop  of Label.t * Insn.binop * pure * pure
  | Pcall   of Label.t * global * pure list * pure list
  | Pdouble of float
  | Pint    of Bitvec.t * Type.imm
  | Pload   of Label.t * Type.basic * pure
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
  | Esw    of pure * local * table
[@@deriving bin_io, compare, equal, sexp]

(** Pretty-prints an expression. *)
val pp : Format.formatter -> t -> unit
