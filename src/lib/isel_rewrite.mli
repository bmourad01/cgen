(** Interface for writing instruction selection rules. *)

open Virtual.Abi

module Pattern : sig
  (** A pattern for a rewrite rule. *)
  type t = private Isel_internal.Pattern.t
  [@@deriving compare, equal, hash, sexp]

  (** Constructs a substitution variable for an arbitrary term. *)
  val var : string -> t

  (** Helpers for constructing patterns. *)
  module Op : sig
    val bop : Insn.binop -> t -> t -> t
    val bool : bool -> t
    val br : t -> t -> t -> t
    val call : t -> t
    val double : float -> t
    val int : Bv.t -> Type.imm -> t
    val i8 : int -> t
    val i16 : int -> t
    val i32 : int32 -> t
    val i64 : int64 -> t
    val hlt : t
    val jmp : t -> t
    val ret : t
    val move : t -> t -> t
    val load : Type.basic -> t -> t
    val store : [Type.basic | `v128] -> t -> t -> t
    val sel : Type.basic -> t -> t -> t -> t
    val single : Float32.t -> t
    val sym : string -> int -> t
    val uop : Insn.unop -> t -> t
    val add : Type.basic -> t -> t -> t
    val div : Type.basic -> t -> t -> t
    val mul : Type.basic -> t -> t -> t
    val mulh : Type.imm -> t -> t -> t
    val rem : Type.basic -> t -> t -> t
    val sub : Type.basic -> t -> t -> t
    val udiv : Type.imm -> t -> t -> t
    val umulh : Type.imm -> t -> t -> t
    val urem : Type.imm -> t -> t -> t
    val and_ : Type.imm -> t -> t -> t
    val or_ : Type.imm -> t -> t -> t
    val asr_ : Type.imm -> t -> t -> t
    val lsl_ : Type.imm -> t -> t -> t
    val lsr_ : Type.imm -> t -> t -> t
    val rol : Type.imm -> t -> t -> t
    val ror : Type.imm -> t -> t -> t
    val xor : Type.imm -> t -> t -> t
    val neg : Type.basic -> t -> t
    val not_ : Type.imm -> t -> t
    val clz : Type.imm -> t -> t
    val ctz : Type.imm -> t -> t
    val popcnt : Type.imm -> t -> t
    val eq : Type.basic -> t -> t -> t
    val ge : Type.basic -> t -> t -> t
    val gt : Type.basic -> t -> t -> t
    val ne : Type.basic -> t -> t -> t
    val le : Type.basic -> t -> t -> t
    val lt : Type.basic -> t -> t -> t
    val o : Type.fp -> t -> t -> t
    val sge : Type.imm -> t -> t -> t
    val sgt : Type.imm -> t -> t -> t
    val sle : Type.imm -> t -> t -> t
    val slt : Type.imm -> t -> t -> t
    val uo : Type.fp -> t -> t -> t
    val fext : Type.fp -> t -> t
    val fibits : Type.fp -> t -> t
    val flag : Type.imm -> t -> t
    val ftosi : Type.fp -> Type.imm -> t -> t
    val ftoui : Type.fp -> Type.imm -> t -> t
    val ftrunc : Type.fp -> t -> t
    val ifbits : Type.imm_base -> t -> t
    val itrunc : Type.imm -> t -> t
    val sext : Type.imm -> t -> t
    val sitof : Type.imm -> Type.fp -> t -> t
    val uitof : Type.imm -> Type.fp -> t -> t
    val zext : Type.imm -> t -> t
    val copy : Type.basic -> t -> t
  end
end

type pattern = Pattern.t

module Subst : sig
  (** A substitition. *)
  type 'r t = private 'r Isel_internal.Subst.t

  val regvar : 'r t -> string -> ('r * Type.basic) option
  val imm : 'r t -> string -> (Bv.t * Type.imm) option
  val single : 'r t -> string -> Float32.t option
  val double : 'r t -> string -> float option
  val sym : 'r t -> string -> (string * int) option
  val label : 'r t -> string -> Label.t option
  val bool : 'r t -> string -> bool option
end

type 'r subst = 'r Subst.t

module Rule(C : Context_intf.S) : sig
  (** A callback for a rule, which takes a substitution and optionally
      returns a list of instructions.

      If the callback returns [None], then the rewrite rule fails to produce
      a match.
  *)
  type ('r, 'i) callback = 'r subst -> 'i list option C.t

  (** A rewrite rule. *)
  type ('r, 'i) t = private ('r, 'i) Isel_internal.Rule(C).t

  (** [pre => post] constructs a rewrite rule where the pattern [pre] is
      matched with an existing program term, and rewritten to the instruction
      sequence produced by [post]. *)
  val (=>) : pattern -> ('r, 'i) callback -> ('r, 'i) t

  (** Same as [=>], but accepts multiple callbacks for matching the same pattern.

      The callbacks are invoked in the order that they are provided, until one
      of them produces a successful match.
  *)
  val (=>*) : pattern -> ('r, 'i) callback list -> ('r, 'i) t

  val (let*!) : 'a option -> ('a -> 'b option C.t) -> 'b option C.t
  val (!!!) : 'a -> 'a option C.t
  val guard : bool -> unit option
end
