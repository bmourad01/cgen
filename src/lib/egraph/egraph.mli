(** An e-graph data structure. *)

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
  type 'a pure =
    | Palloc  of 'a * int
    | Pbinop  of 'a * Insn.binop * 'a pure * 'a pure
    | Pbool   of bool
    | Pcall   of 'a * Type.basic * 'a global * 'a pure list * 'a pure list
    | Pdouble of float
    | Pint    of Bv.t * Type.imm
    | Pload   of 'a * Type.basic * 'a pure
    | Psel    of 'a * Type.basic * 'a pure * 'a pure * 'a pure
    | Psingle of Float32.t
    | Psym    of string * int
    | Punop   of 'a * Insn.unop * 'a pure
    | Pvar    of Var.t
  [@@deriving bin_io, compare, equal, sexp]

  (** A global control-flow destination. *)
  and 'a global =
    | Gaddr of Bv.t
    | Gpure of 'a pure
    | Gsym  of string
  [@@deriving bin_io, compare, equal, sexp]

  (** A local control-flow destination. *)
  and 'a local = Label.t * 'a pure list
  [@@deriving bin_io, compare, equal, sexp]

  (** A control-flow destination. *)
  and 'a dst =
    | Dglobal of 'a global
    | Dlocal  of 'a local
  [@@deriving bin_io, compare, equal, sexp]

  (** A switch table. *)
  type 'a table = (Bv.t * 'a local) list
  [@@deriving bin_io, compare, equal, sexp]

  (** A "base" expression, which corresponds directly to a [Virtual]
      instruction. *)
  type 'a t =
    | Ebr      of 'a pure * 'a dst * 'a dst
    | Ecall    of 'a global * 'a pure list * 'a pure list
    | Ejmp     of 'a dst
    | Eret     of 'a pure
    | Eset     of Var.t * 'a pure
    | Estore   of Type.basic * 'a pure * 'a pure
    | Esw      of Type.imm * 'a pure * 'a local * 'a table
  [@@deriving bin_io, compare, equal, sexp]
end

type 'a exp = 'a Exp.t [@@deriving compare, equal, sexp]

(** A callback [f] where [f ~parent x] returns [true] if [parent]
    dominates [x]. *)
type 'a dominance = parent:'a -> 'a -> bool

(** An e-graph, where ['a] is the type used to establish provenance
    between expressions and node IDs. *)
type 'a t

type 'a egraph = 'a t

(** Constructs an e-graph. *)
val create : dominance:'a dominance -> 'a t

(** A component of a rule. *)
type query [@@deriving compare, equal, sexp]

(** A substitution environment from query variables to IDs. *)
type subst = id String.Map.t

(** A callback that can be invoked when applying a rule. *)
type ('a, 'b) callback = 'a t -> id -> subst -> 'b

(** A rewrite rule. *)
type 'a rule

module Rule : sig
  type 'a t = 'a rule

  (** [var x] constructs a substitition for variable [x]. *)
  val var : string -> query

  (** [exp op] is equivalent to [op & []]. *)
  val exp : Enode.op -> query

  (** [op & args] constructs an substitution for [op] and [args]. *)
  val (&) : Enode.op -> query list -> query

  (** [pre => post] constructs a rewrite rule where expressions
      matching [pre] shall be rewritten to [post]. *)
  val (=>) : query -> query -> 'a t

  (** [(pre =>? post) ~if_] is similar to [pre => post], but the
      rule is applied conditionally according to [if_]. *)
  val (=>?) : query -> query -> if_:(('a, bool) callback) -> 'a t

  (** [pre => gen] allows a post-condition to be generated
      dynamically according to [gen]. *)
  val (=>*) : query -> ('a, query option) callback -> 'a t
end

(** Adds an expression to the e-graph and returns its corresponding ID. *)
val add : 'a t -> 'a exp -> id

(** Returns the analysis data for a given ID. *)
val data : 'a t -> id -> const option

(** [find_exn eg id] returns the representative element for [id] in [eg],
    if it exists.

    @raise Invalid_argument if [id] is not present in [eg].
*)
val find_exn : 'a t -> id -> id

(** Same as [find_exn eg id], but returns [None] if [id] is not present. *)
val find : 'a t -> id -> id option

(** [provenance eg id] finds the provenance associated with [id] in [eg],
    if it exists. *)
val provenance : 'a t -> id -> 'a option

type 'a extractor

(** Extracts optimized terms from the e-graph based on the [cost]
    heuristic function. *)
module Extractor : sig
  (** A cost heuristic.

      [child] provides a callback for calculating the cost of the
      children of the e-node.

      @raise Failure if [child] is called for an ID that doesn't exist.
  *)
  type cost = child:(id -> int) -> enode -> int

  type 'a t = 'a extractor

  (** Initialize the extractor. *)
  val init : 'a egraph -> cost:cost -> 'a t

  (** Extract the term associated with an ID in the provided
      e-graph.

      Returns an error if the ID does not exist or the resulting term is
      not well-formed.
  *)
  val extract : 'a t -> id -> 'a exp Or_error.t

  (** Same as [extract t id].

      @raise Invalid_argument if the ID does not exist or the resulting
      term is not well-formed.
  *)
  val extract_exn : 'a t -> id -> 'a exp
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
val fixpoint : ?sched:scheduler -> ?fuel:int -> 'a t -> 'a rule list -> bool
