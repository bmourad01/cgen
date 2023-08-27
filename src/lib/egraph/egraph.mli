(** An e-graph data structure.

    The e-graph allows us to track equivalent terms in a function and
    simultaneously apply rewrite rules on these terms, which solves
    the phase-ordering problem.

    This enables us to do several key optimizations, such as common
    subexpression elimination, loop-invariant code motion, constant
    folding, constant propagation, store-to-load forwarding, strength
    reduction, and so on.

    The implementation used is a slightly less-powerful version of
    a standard e-graph known as an "acyclic e-graph". This technique
    was first seen in the Cranelift compiler and proves to be a decent
    trade-off between expressivity and efficiency. Specifically, it
    allows us to avoid an expensive fixpoint loop to maintain the
    invariants of the data structure and instead apply all the rewrites
    in a single, carefully-ordered pass over the dominator tree of the
    function.
*)

open Core
open Regular.Std
open Virtual

module Id : sig
  type t = private int

  include Regular.S with type t := t
end

(** An identifier for an e-class. *)
type id = Id.t [@@deriving compare, equal, hash, sexp]

(** Expression trees with provenance tracking. *)
module Exp : sig
  (** A "pure" expression. *)
  type pure =
    | Pbinop  of Label.t option * Insn.binop * pure * pure
    | Pbool   of bool
    | Pdouble of float
    | Pint    of Bv.t * Type.imm
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
    | Gsym  of string * int
  [@@deriving bin_io, compare, equal, sexp]

  (** A local control-flow destination. *)
  type local = Label.t * pure list
  [@@deriving bin_io, compare, equal, sexp]

  (** A control-flow destination. *)
  type dst =
    | Dglobal of global
    | Dlocal  of local
  [@@deriving bin_io, compare, equal, sexp]

  (** A switch table. *)
  type table = (Bv.t * local) list
  [@@deriving bin_io, compare, equal, sexp]

  (** A "base" expression, which corresponds directly to a [Virtual]
      instruction. *)
  type t =
    | Ebr      of pure * dst * dst
    | Ecall    of (Var.t * Type.basic) option * global * pure list * pure list
    | Ejmp     of dst
    | Eload    of Var.t * Type.basic * pure
    | Eret     of pure
    | Eset     of Var.t * pure
    | Estore   of Type.basic * pure * pure
    | Esw      of Type.imm * pure * local * table
    | Evaarg   of Var.t * Type.basic * pure
    | Evastart of pure
  [@@deriving bin_io, compare, equal, sexp]

  val pp_pure : Format.formatter -> pure -> unit
  val pp_global : Format.formatter -> global -> unit
  val pp_local : Format.formatter -> local -> unit
  val pp_dst : Format.formatter -> dst -> unit
  val pp : Format.formatter -> t -> unit
end

type exp = Exp.t [@@deriving bin_io, compare, equal, sexp]

val pp_exp : Format.formatter -> exp -> unit

(** An e-graph. *)
type t
type egraph = t

(** A substitution environment from pattern variables to IDs. *)
type subst = id String.Map.t

(** A component of a rule. *)
type pattern [@@deriving compare, equal, sexp]

(** A callback that can be invoked when applying a rule. *)
type 'a callback = t -> subst -> 'a

(** A rewrite rule. *)
type rule

(** A table of rules. *)
type rules

(** Creates a table from a list of rules.

    @raise Invalid_argument if there is a rule where the precondition is
    simply a variable.
*)
val create_table : rule list -> rules

(** [create fn tenv rules ?fuel] constructs an e-graph from a function [fn]
    and applies the [rules] eagerly.

    [tenv] is the typing environment of the module that [fn] belongs to.

    [fuel] is the maximum rewrite depth. This is to limit state explosion
    since rewrites are themselves recursively rewritten. Note that if
    [fuel < 0], then no rewrite rules will be applied.

    [fn] is expected to be in SSA form.
*)
val create : ?fuel:int -> func -> Typecheck.env -> rules -> t Or_error.t

(** Returns the constant associated with the e-class ID. *)
val const : t -> id -> const option

(** Returns the type associated with the e-class ID. *)
val typeof : t -> id -> Type.t option

module Rule : sig
  type t = rule

  (** [var x] constructs a substitution for variable [x]. *)
  val var : string -> pattern

  (** [pre => post] constructs a rewrite rule where expressions
      matching [pre] shall be rewritten to [post]. *)
  val (=>) : pattern -> pattern -> t

  (** [(pre =>? post) ~if_] is similar to [pre => post], but the
      rule is applied conditionally according to [if_]. *)
  val (=>?) : pattern -> pattern -> if_:(bool callback) -> t

  (** [pre =>* gen] allows a post-condition to be generated
      dynamically according to [gen]. *)
  val (=>*) : pattern -> pattern option callback -> t

  (** Helpers for constructing patterns. *)
  module Op : sig
    val bop : Insn.binop -> pattern -> pattern -> pattern
    val bool : bool -> pattern
    val br : pattern -> pattern -> pattern -> pattern
    val double : float -> pattern
    val int : Bv.t -> Type.imm -> pattern
    val i8 : int -> pattern
    val i16 : int -> pattern
    val i32 : int32 -> pattern
    val i64 : int64 -> pattern
    val jmp : pattern -> pattern
    val sel : Type.basic -> pattern -> pattern -> pattern -> pattern
    val single : Float32.t -> pattern
    val sym : string -> int -> pattern
    val uop : Insn.unop -> pattern -> pattern
    val add : Type.basic -> pattern -> pattern -> pattern
    val div : Type.basic -> pattern -> pattern -> pattern
    val mul : Type.basic -> pattern -> pattern -> pattern
    val mulh : Type.imm -> pattern -> pattern -> pattern
    val rem : Type.basic -> pattern -> pattern -> pattern
    val sub : Type.basic -> pattern -> pattern -> pattern
    val udiv : Type.imm -> pattern -> pattern -> pattern
    val umulh : Type.imm -> pattern -> pattern -> pattern
    val urem : Type.imm -> pattern -> pattern -> pattern
    val and_ : Type.imm -> pattern -> pattern -> pattern
    val or_ : Type.imm -> pattern -> pattern -> pattern
    val asr_ : Type.imm -> pattern -> pattern -> pattern
    val lsl_ : Type.imm -> pattern -> pattern -> pattern
    val lsr_ : Type.imm -> pattern -> pattern -> pattern
    val rol : Type.imm -> pattern -> pattern -> pattern
    val ror : Type.imm -> pattern -> pattern -> pattern
    val xor : Type.imm -> pattern -> pattern -> pattern
    val neg : Type.basic -> pattern -> pattern
    val not_ : Type.imm -> pattern -> pattern
    val clz : Type.imm -> pattern -> pattern
    val ctz : Type.imm -> pattern -> pattern
    val popcnt : Type.imm -> pattern -> pattern
    val eq : Type.basic -> pattern -> pattern -> pattern
    val ge : Type.basic -> pattern -> pattern -> pattern
    val gt : Type.basic -> pattern -> pattern -> pattern
    val ne : Type.basic -> pattern -> pattern -> pattern
    val le : Type.basic -> pattern -> pattern -> pattern
    val lt : Type.basic -> pattern -> pattern -> pattern
    val o : Type.fp -> pattern -> pattern -> pattern
    val sge : Type.imm -> pattern -> pattern -> pattern
    val sgt : Type.imm -> pattern -> pattern -> pattern
    val sle : Type.imm -> pattern -> pattern -> pattern
    val slt : Type.imm -> pattern -> pattern -> pattern
    val uo : Type.fp -> pattern -> pattern -> pattern
    val fext : Type.fp -> pattern -> pattern
    val fibits : Type.fp -> pattern -> pattern
    val flag : Type.imm -> pattern -> pattern
    val ftosi : Type.fp -> Type.imm -> pattern -> pattern
    val ftoui : Type.fp -> Type.imm -> pattern -> pattern
    val ftrunc : Type.fp -> pattern -> pattern
    val ifbits : Type.imm_base -> pattern -> pattern
    val itrunc : Type.imm -> pattern -> pattern
    val sext : Type.imm -> pattern -> pattern
    val sitof : Type.imm -> Type.fp -> pattern -> pattern
    val uitof : Type.imm -> Type.fp -> pattern -> pattern
    val zext : Type.imm -> pattern -> pattern
    val copy : Type.basic -> pattern -> pattern
  end
end

type extractor

(** Extracts optimized terms from the e-graph. *)
module Extractor : sig
  type t = extractor

  (** Initialize the extractor. *)
  val init : egraph -> t

  (** Extract the term associated with a label in the provided e-graph.

      If the resulting term is not well-formed, an error is returned.
      If there is no term associated with the label, [None] is returned.
  *)
  val term : t -> Label.t -> exp option Or_error.t

  (** Same as [term t l].

      @raise Invalid_argument if the the resulting term is not well-formed.
  *)
  val term_exn : t -> Label.t -> exp option

  (** [cfg t] attempts to extract the terms in the underlying e-graph
      back to the input function. *)
  val cfg : t -> func Context.t
end
