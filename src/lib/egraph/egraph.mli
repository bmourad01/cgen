(** An e-graph data structure for performing equality saturation.

    The main motivation for using this data structure is that it allows
    us to keep track of equivalent program terms, as well as iteratively
    apply rewrite rules, in a relatively efficient and principled way
    that solves the phase ordering problem.
*)

open Core
open Regular.Std
open Virtual

module Id : sig
  type t = private int

  include Regular.S with type t := t
end

(** A unique identifier. *)
type id = Id.t [@@deriving compare, equal, hash, sexp]

(** An e-node.

    This is a specialized form for each operation in a [Virtual] program,
    where any possible operation is associated with zero or more children.
*)
type enode [@@deriving compare, equal, hash, sexp]

module Enode : sig
  (** A special form for each instruction type in a [Virtual] program. *)
  type op =
    | Oaddr     of Bv.t
    | Oalloc    of int
    | Obinop    of Insn.binop
    | Obool     of bool
    | Obr
    | Ocall0
    | Ocall     of Type.basic
    | Ocallargs
    | Odouble   of float
    | Ojmp
    | Oint      of Bv.t * Type.imm
    | Oload     of Type.basic
    | Olocal    of Label.t
    | Oret
    | Osel      of Type.basic
    | Oset      of Var.t
    | Osingle   of Float32.t
    | Ostore    of Type.basic
    | Osw       of Type.imm
    | Osym      of string * int
    | Otbl      of Bv.t
    | Ounop     of Insn.unop
    | Ovar      of Var.t
  [@@deriving compare, equal, hash, sexp]

  type t = enode [@@deriving compare, equal, hash, sexp]

  (** The operator of the e-node. *)
  val op : t -> op

  (** The children of the e-node. *)
  val children : t -> id list

  val pp_op : Format.formatter -> op -> unit
end

(** Expression trees with provenance tracking. *)
module Exp : sig
  (** A "pure" expression. *)
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
    | Ecall    of global * pure list * pure list
    | Ejmp     of dst
    | Eret     of pure
    | Eset     of Var.t * pure
    | Estore   of Type.basic * pure * pure
    | Esw      of Type.imm * pure * local * table
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

(** Constructs an e-graph from a function. *)
val create : func -> t Or_error.t

(** A component of a rule. *)
type query [@@deriving compare, equal, sexp]

(** A substitution environment from query variables to IDs. *)
type subst = id String.Map.t

(** A callback that can be invoked when applying a rule. *)
type 'a callback = t -> id -> subst -> 'a

(** A rewrite rule. *)
type rule

module Rule : sig
  type t = rule

  (** [var x] constructs a substitition for variable [x]. *)
  val var : string -> query

  (** [exp op] is equivalent to [op & []]. *)
  val exp : Enode.op -> query

  (** [op & args] constructs an substitution for [op] and [args]. *)
  val (&) : Enode.op -> query list -> query

  (** [pre => post] constructs a rewrite rule where expressions
      matching [pre] shall be rewritten to [post]. *)
  val (=>) : query -> query -> t

  (** [(pre =>? post) ~if_] is similar to [pre => post], but the
      rule is applied conditionally according to [if_]. *)
  val (=>?) : query -> query -> if_:(bool callback) -> t

  (** [pre => gen] allows a post-condition to be generated
      dynamically according to [gen]. *)
  val (=>*) : query -> query option callback -> t
end

(** Returns the analysis data for a given ID. *)
val data : t -> id -> const option

type extractor

(** Extracts optimized terms from the e-graph based on the [cost]
    heuristic function. *)
module Extractor : sig
  (** A cost heuristic.

      [child] provides a callback for calculating the cost of the
      children of the e-node.

      @raise Failure if [child] is called for an ID that doesn't exist.
  *)
  type cost = child:(id -> int) -> enode -> int

  type t = extractor

  (** Initialize the extractor. *)
  val init : egraph -> cost:cost -> t

  (** Extract the term associated with a label in the provided e-graph.

      If the resulting term is not well-formed, an error is returned.
      If there is no term associated with the label, [None] is returned.
  *)
  val term : t -> Label.t -> exp option Or_error.t

  (** Same as [extract t l].

      @raise Invalid_argument if the the resulting term is not well-formed.
  *)
  val term_exn : t -> Label.t -> exp option

  (** [reify t] attempts to extract the terms in the underlying e-graph
      back to the input function .*)
  val reify : t -> func Context.t
end

(** Parameters for scheduling which rules should be applied at a given
    time.

    This is useful for preventing blowup of infinitely-sized terms when
    applying certain classes of rewrite rules.
*)
type scheduler

module Scheduler : sig
  type t = scheduler

  (** Creates the parameters for the scheduler.

      [match_limit] limits the number of matches that a rule can produce
      before being "banned" for a fixed number of iterations.

      [ban_length] is the number of iterations for which a rule is "banned"
      from being applied.

      @raise Invalid_argument if [match_limit < 1] or [ban_length < 1].
  *)
  val create_exn : ?match_limit:int -> ?ban_length:int -> unit -> t
end

(** [fixpoint t rules ?sched ?fuel] repeatedly applies [rules] to the
    e-graph until a fixed-point is reached, [fuel] iterations have
    occurred, or the [sched] parameters indicate that the algorithm
    should terminate.

    Returns [true] if a fixed-point was reached.

    By default, [fuel] is set to [Int.max_value]. If [fuel <= 1] then at
    least one iteration is performed.
*)
val fixpoint : ?sched:scheduler -> ?fuel:int -> t -> rule list -> bool
