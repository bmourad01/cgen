(** An e-graph data structure. *)

open Core
open Virtual
open Regular.Std

module Id : sig
  type t = private int

  include Regular.S with type t := t
end

(** A unique identifier. *)
type id = Id.t [@@deriving compare, equal, hash, sexp]

(** An e-node. *)
type enode [@@deriving compare, equal, hash, sexp]

module Enode : sig
  type op =
    | Oalloc  of int
    | Obinop  of Insn.binop
    | Obool   of bool
    | Obr
    | Ocall0
    | Ocall   of Type.basic
    | Odouble of float
    | Odst    of dst
    | Oglobal of global
    | Ojmp
    | Oint    of Bv.t * Type.imm
    | Oload   of Type.basic
    | Olocal  of Label.t
    | Oret
    | Osel    of Type.basic
    | Osingle of Float32.t
    | Ostore  of Type.basic
    | Osw     of Type.imm
    | Osym    of string * int
    | Ounop   of Insn.unop
    | Ovar    of Var.t
  [@@deriving compare, equal, hash, sexp]

  and global =
    | Gaddr   of Bv.t
    | Gop     of op
    | Gsym    of string
  [@@deriving compare, equal, hash, sexp]

  and dst =
    | Dglobal of global
    | Dlocal  of Label.t
  [@@deriving compare, equal, hash, sexp]

  type t = enode [@@deriving compare, equal, hash, sexp]

  (** The operator of the e-node. *)
  val op : t -> op

  (** The children of the e-node. *)
  val children : t -> Id.t list

  val pp_op : Format.formatter -> op -> unit
  val pp_global : Format.formatter -> global -> unit
  val pp_dst : Format.formatter -> dst -> unit
end

(** An expression *)
type exp [@@deriving compare, equal, sexp]

val pp_exp : Format.formatter -> exp -> unit

module Exp : sig
  type t = exp [@@deriving compare, equal, sexp]

  val pp : Format.formatter -> t -> unit

  (** The operator of the expression. *)
  val op : t -> Enode.op

  (** The arguments of the expression. *)
  val args : t -> t list

  (** [exp op] is equivalent to [op & []]. *)
  val exp : Enode.op -> t

  (** [op & args] constructs an expression. *)
  val (&) : Enode.op -> t list -> t
end

(** An e-graph. *)
type t

type egraph = t

(** Constructs an e-graph. *)
val create : unit -> t

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

(** Adds an expression to the e-graph and returns its ID. *)
val add : t -> exp -> id

(** Returns the analysis data for a given ID. *)
val data : t -> id -> const option

(** [find_exn eg id] returns the representative element for [id] in [eg],
    if it exists.

    @raise Invalid_argument if [id] is not present in [eg].
*)
val find_exn : t -> id -> id

(** Same as [find_exn eg id], but returns [None] if [id] is not present. *)
val find : t -> id -> id option

(** A cost heuristic.

    [child] provides a callback for calculating the cost of the
    children of the e-node.

    @raise Failure if [child] is called for an ID that doesn't exist.
*)
type cost = child:(id -> int) -> enode -> int

type extractor

(** Extracts optimized terms from the e-graph based on the [cost]
    heuristic function. *)
module Extractor : sig
  type t = extractor

  (** Initialize the extractor. *)
  val init : egraph -> cost:cost -> t

  (** Extract the term associated with an ID in the provided
      e-graph.

      Returns [None] if the ID does not exist.
  *)
  val extract : t -> id -> exp option

  (** Same as [extract t id].

      @raise Invalid_argument if the ID does not exist.
  *)
  val extract_exn : t -> id -> exp
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
    e-graph until a fixed-point is reached, [fuel < 0], or the [sched]
    parameters indicate that the algorithm should terminate.

    Returns [true] if a fixed-point was reached.
*)
val fixpoint : ?sched:scheduler -> ?fuel:int -> t -> rule list -> bool
