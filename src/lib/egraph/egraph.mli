(** An e-graph-based optimizer.

    The e-graph allows us to track equivalent terms in a function and
    simultaneously apply rewrite rules on these terms, which solves
    the phase-ordering problem.

    This enables us to do several key optimizations within a single,
    unified framework, such as common subexpression elimination,
    loop-invariant code motion, constant folding, constant propagation,
    store-to-load forwarding, redundant load elimination, strength
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

open Virtual

(** A substitution environment for pattern variables. *)
module Subst : sig
  (** Information about the matched variable. *)
  type info

  (** The substiution environment. *)
  type t

  (** Performs a lookup of the variable. *)
  val find : t -> string -> info option

  (** The constant for the varialbe, if it is known. *)
  val const : info -> const option

  (** The type of the variable, if it is known. *)
  val typeof : info -> Type.t option
end

type subst = Subst.t

(** A component of a rule. *)
type pattern [@@deriving compare, equal, sexp]

(** A callback that can be invoked when applying a rule. *)
type 'a callback = subst -> 'a

(** A rewrite rule. *)
type rule

(** A table of rules. *)
type rules

(** Creates a table from a list of rules.

    @raise Invalid_argument if there is a rule where the precondition is
    simply a variable.
*)
val create_table : rule list -> rules

(** [run fn tenv rules ?depth_limit ?match_limit] constructs an e-graph
    from a function [fn] and applies the [rules] eagerly to produce a
    transformed function.

    [tenv] is the typing environment of the module that [fn] belongs to.

    [depth_limit] is the maximum rewrite depth. This is to limit state
    explosion since rewrites are themselves recursively rewritten. Note
    that if [depth_limit < 0], then no rewrite rules will be applied.

    [match_limit] is the maximum number of matches/rewrites allowed per
    term. This is to limit state explosion since all versions of all
    classes of terms are considered for rewrites. Higher values for
    this parameter may significantly increase running time. Note that
    if [match_limit <= 0] then no rewrite rules will be applied.

    [fn] is expected to be in SSA form.
*)
val run :
  ?depth_limit:int ->
  ?match_limit:int ->
  func ->
  Typecheck.env ->
  rules ->
  func Context.t

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
