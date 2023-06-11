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

(** A cost heuristic. *)
type cost = (id -> int) -> enode -> int

(** Extracts an expression from an ID. *)
type extractor = id -> exp

(** Performs term extraction. *)
val extract : t -> cost:cost -> extractor

(** Applies a list of rewrite rules to the e-graph. *)
val apply : t -> rule list -> unit

(** [fixpoint t rules ?fuel] repeatedly calls [apply t rules] until
    a fixed-point is reached, or [fuel] is exhausted.

    Returns [true] if a fixed-point was reached.
*)
val fixpoint : ?fuel:int -> t -> rule list -> bool
