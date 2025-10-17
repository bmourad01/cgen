open Core

(** The input language. *)
module type L = sig
  (** The type for operations in the input language. *)
  type op [@@deriving compare, equal, hash, sexp]

  (** A term, which is the subject of attempting to match
      against a pattern. *)
  type term

  (** An identifier for a term.

      It is assumed that terms are interned as [id]s.
  *)
  type id [@@deriving equal]

  (** Returns [true] if the [op] has the commutative property.

      It is assumed that commutative [op]s are always binary
      in their operands.
  *)
  val is_commutative : op -> bool

  (** Return the [op] of the term, if applicable. *)
  val term_op : term -> op option

  (** Return the arguments (children) of the term.

      If the term has no arguments, then it is considered a {i ground} term.
  *)
  val term_args : term -> id list

  (** If this term is a {i union} of two terms (i.e. an equivalence class),
      then return the pair of node IDs that represents the equivalence.

      The first element is the {i pre} term, and the second element is the
      {i post} term

      The {i post} term represents the newer term, and will be prioritized
      in when looking for matches. Meanwhile, the {i pre} term will be
      bookmarked for later exploration.
  *)
  val term_union : term -> (id * id) option

  (** Pretty-print a term ID. *)
  val pp_id : Format.formatter -> id -> unit

  (** Pretty-print an operation. *)
  val pp_op : Format.formatter -> op -> unit
end

(** Create a matcher. *)
module Make(M : L) : sig
  open M

  (** A pattern to be inserted in to the matcher.

      [V x]: a substitution variable [x]

      [P (op, children)]: a concrete pattern for operation [op],
      with arguments [children] as subpatterns. If [children = []],
      then this is considered a {i ground} pattern.
  *)
  type pat =
    | V of string
    | P of op * pat list
  [@@deriving compare, equal, hash, sexp]

  val pp_pat : Format.formatter -> pat -> unit

  (** A compiled VM program. *)
  type 'a program

  (** Pretty-print the program. *)
  val pp_program : Format.formatter -> 'a program -> unit

  (** Compile a set of rules into a program.

      Each rule is a pattern [pat], and an associated payload
      for when [pat] successfully matches.

      If [commute] is [true] (default is [false]), then patterns
      will be expanded/permuted according to [M.is_commutative].
      This can substantially increase the size of the compiled
      program.

      The rules are assumed to be in an {i optimal} priority order,
      and the [VM] (see below) will prioritize yielding matches in
      this order.
  *)
  val compile : ?commute:bool -> (pat * 'a) list -> 'a program

  (** Returns [true] is the program is empty. *)
  val is_empty : 'a program -> bool

  (** A substitution.

      Keys are substitution variables, and values are the [term]-[id] pairs.
  *)
  type subst = id String.Map.t

  (** A successful match. *)
  type 'a yield

  (** Debug printing for a yield.

      The first argument is a pretty-printer for terms, given an id.
  *)
  val pp_yield_dbg :
    (Format.formatter -> id -> unit) ->
    Format.formatter ->
    'a yield ->
    unit

  module Yield : sig
    type 'a t = 'a yield

    (** The resulting substitution. *)
    val subst : 'a t -> subst

    (** The resulting payload. *)
    val payload : 'a t -> 'a

    (** The rule ordinal that produced the result. *)
    val rule : 'a t -> int

    (** The pattern that was matched. *)
    val pat : 'a t -> pat
  end

  (** A virtual machine (VM) for running a compiled program. *)
  module VM : sig
    (** Internal VM state. *)
    type state

    (** Create a VM state.

        [registers] is the initial capacity of the register file,
        i.e. the number of subterms that the VM will need to keep
        track of at any given time. The register file will grow
        as needed, so this number should be informed by the relative
        size of the patterns for the input program.
    *)
    val create : ?registers:int -> unit -> state

    (** Reset the VM state.

        This should be done after all matching on a single term
        is completed.
    *)
    val reset : state -> unit

    (** The ID of the term that was passed to [init].

        @raise Failure if the VM was uninitialized
    *)
    val root : state -> id

    (** Initializes the state for incremental execution on a
        single term.

        Returns [true] if the initialization was successful.
    *)
    val init : lookup:(id -> term) -> state -> 'a program -> id -> bool

    (** Attempts to produce a single match.

        Returns [None] if the term had no matches.
    *)
    val one : state -> 'a program -> 'a yield option

    (** A generalized version of [one].

        The reulting list of matches is provided in the order of the
        provided rules during compilation.

        An optional [limit] on the number of matches can be provided. If
        this is less than [1], then no matches will be produced.
    *)
    val many : ?limit:int -> state -> 'a program -> 'a yield list
  end
end
