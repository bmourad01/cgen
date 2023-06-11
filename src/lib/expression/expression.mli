(** A representation of Virtual instructions as an expression tree.

    Given a sequence of instructions, a maximal DAG is formed according
    to control and data flow throughout a function.

    The motivation for this data representation is to allow for easy
    pattern matching across (and within) basic blocks. Uses may include
    performing certain optimizations, instruction selection, and so on.
*)

open Core
open Regular.Std
open Virtual

(** A subexpression used to compute the result of an instruction.

    If the expression wasn't a pure operand, then it may optionally
    contain a label corresponding to an instruction. This is to maintain
    provenance with the CFG representation of the program where possible.

    Transformations to expressions can omit this label, in which case
    fresh label-variable pairs will be generated, given a compilation
    context. Otherwise, updates to terms sharing the same label are
    expected to be (syntactically) equal.
*)
type pure =
  | Palloc  of Label.t option * int
  | Pbinop  of Label.t option * Insn.binop * pure * pure
  | Pbool   of bool
  | Pcall   of Label.t option * Type.basic * global * pure list * pure list
  | Pdouble of float
  | Pint    of Bv.t * Type.imm
  | Pload   of Label.t option * Type.basic * pure
  | Psel    of Label.t option * Type.basic * pure * pure * pure
  | Psingle of Float32.t
  | Psym    of string * int
  | Punop   of Label.t option * Insn.unop * pure
  | Pvar    of Var.t
[@@deriving bin_io, compare, equal, sexp]

(** A global control-flow destination. *)
and global =
  | Gaddr of Bv.t
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
type table = (Bv.t * local) list
[@@deriving bin_io, compare, equal, sexp]

(** An expression. *)
type t =
  | Ebr      of pure * dst * dst
  | Ecall    of global * pure list * pure list
  | Ehlt
  | Ejmp     of dst
  | Eret     of pure option
  | Eset     of Var.t * pure
  | Estore   of Type.basic * pure * pure
  | Esw      of Type.imm * pure * local * table
  | Evaarg   of Var.t * Type.basic * Var.t
  | Evastart of Var.t
[@@deriving bin_io, compare, equal, sexp]

(** Pretty-prints an expression. *)
val pp : Format.formatter -> t -> unit

(** Partially evaluates an expression, with an optional environment
    for free variables. *)
val eval : ?env:pure Var.Map.t -> t -> t

val eval_pure : ?env:pure Var.Map.t -> pure -> pure
val eval_global : ?env:pure Var.Map.t -> global -> global
val eval_local : ?env:pure Var.Map.t -> local -> local
val eval_dst : ?env:pure Var.Map.t -> dst -> dst

(** Returns the set of free variables occurring in an expression. *)
val free_vars : t -> Var.Set.t

val free_vars_of_pure : pure -> Var.Set.t
val free_vars_of_global : global -> Var.Set.t
val free_vars_of_local : local -> Var.Set.t
val free_vars_of_dst : dst -> Var.Set.t
val free_vars_of_table : table -> Var.Set.t

(** Returns the set of labels occurring in an expression. These
    correspond to instruction labels in the function that the
    expression was built from.

    Note, this set does not include labels that are destinations
    for control-flow operations.
*)
val labels : t -> Label.Set.t

val labels_of_pure : pure -> Label.Set.t
val labels_of_global : global -> Label.Set.t
val labels_of_local : local -> Label.Set.t
val labels_of_dst : dst -> Label.Set.t
val labels_of_table : table -> Label.Set.t

(** The expression-building context for a function. *)
type ctx

(** Creates the context for a function. *)
val init : func -> ctx Or_error.t

(** The name of the function that was used to create the context. *)
val func : ctx -> string

(** A resolved label.

    [`blk b]: the label corresponds to the control instruction
    of block [b] (and is equivalent to [Blk.label b]).

    [`insn (i, b, x)]: the label corresponds to instruction [i] in
    block [b], and an optional variable [x] that is assigned the
    result.
*)
type resolved = [
  | `blk of blk
  | `insn of insn * blk * Var.t option
]

(** Resolves the label in the given context. *)
val resolve : ctx -> Label.t -> resolved option

(** Returns the currently known dependents of a label. *)
val dependents : ctx -> Label.t -> (Label.t * Var.t) seq

(** Returns the currently known dependencies of a label. *)
val dependencies : ctx -> Label.t -> (Label.t * Var.t) seq

(** Pretty-prints the dependency graph in Graphviz DOT notation. *)
val pp_deps : Format.formatter -> ctx -> unit

(** [get ctx l] attempts to construct an expression based on
    the label [l] in function [fn]. The results are memoized in
    [ctx].

    [l] must refer to either a block, in which case the expression
    is built starting from the control instruction, or a regular
    data instruction.

    The algorithm walks backwards and constructs a maximal DAG,
    substituting in subexpressions for variables when possible.

    Note that [fn] is assumed to be type-checked and in SSA form.
*)
val get : ctx -> Label.t -> t Or_error.t

(** Same as [build], but runs for every instruction in the
    context. *)
val fill : ctx -> unit Or_error.t

(** [map_exp ctx l ~f] maps a single expression associated with label
    [l] according to [f]. This is a mutable update to [ctx].

    If [l] doesn't exist in [ctx], then no changes are made.

    @raise Failure if [ctx] is mutated within the body of [f].
*)
val map_exp : ctx -> Label.t -> f:(t -> t) -> unit Context.t

(** [map ctx ~f] transforms each expression in the context according
    to [f]. This is a mutable update to [ctx].

    @raise Failure if [ctx] is mutated within the body of [f].
*)
val map : ctx -> f:(Label.t -> t -> t) -> unit Context.t

(** Information about reifying an expression back to a [Virtual]
    datatype. *)
module Reify : sig
  (** An expression corresponds to either a data or control-flow
      instruction. *)
  type elt = [
    | `insn of Insn.op
    | `ctrl of ctrl
  ]

  (** The environment constructed from reifying an expression. *)
  type env

  (** The empty enviromnent. *)
  val empty : env

  (** Gets the reified instruction corresponding to a label. *)
  val get : Label.t -> env -> elt Or_error.t

  (** Returns the contents of the environment. *)
  val enum : env -> (Label.t * elt) seq
end

(** [reify ctx l ~init] returns the environment from reifying the
    expression at label [l] in the given context [ctx].

    An optional starting enviromnent [init] can be provided to
    avoid redundant computations.
*)
val reify : ?init:Reify.env -> ctx -> Label.t -> Reify.env Or_error.t

(** [reify_to_fn ctx fn] transforms [fn] according to the expressions
    available to the context [ctx].

    It is assumed that [fn] was used to generate [ctx].
*)
val reify_to_fn : ctx -> func -> func Or_error.t
