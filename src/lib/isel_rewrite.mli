(** Interface for writing instruction selection rules. *)

module Pattern : sig
  (** A witness for expression patterns. *)
  type exp

  (** A witness for statement patterns. *)
  type stmt

  (** A pattern for a rewrite rule, where ['a] is the type of
      pattern being constructed, and ['b] is the type of its
      sub-patterns.
  *)
  type ('a, 'b) t = private ('a, 'b) Isel_internal.Pattern.t

  (** A toplevel pattern. *)
  type toplevel = (stmt, exp) t

  (** A sub-pattern. *)
  type sub = (exp, exp) t

  (** Constructs a substitution variable for an arbitrary term. *)
  val var : string -> sub

  (** Helpers for constructing patterns. *)
  module Op : sig
    (** Toplevel instructions. *)

    val store : [Type.basic | `v128] -> sub -> sub -> toplevel
    val br : sub -> sub -> sub -> toplevel
    val call : sub -> toplevel
    val hlt : toplevel
    val jmp : sub -> toplevel
    val ret : toplevel
    val move : sub -> sub -> toplevel

    (** Constants. *)

    val bool : bool -> sub
    val double : float -> sub
    val int : Bv.t -> Type.imm -> sub
    val i8 : int -> sub
    val i16 : int -> sub
    val i32 : int32 -> sub
    val i64 : int64 -> sub
    val single : Float32.t -> sub
    val sym : string -> int -> sub

    (** Loads. *)

    val load : Type.basic -> sub -> sub

    (** Conditional selection. *)

    val sel : Type.basic -> sub -> sub -> sub -> sub

    (** Binary operators. *)

    val add : Type.basic -> sub -> sub -> sub
    val div : Type.basic -> sub -> sub -> sub
    val mul : Type.basic -> sub -> sub -> sub
    val mulh : Type.imm -> sub -> sub -> sub
    val rem : Type.basic -> sub -> sub -> sub
    val sub : Type.basic -> sub -> sub -> sub
    val udiv : Type.imm -> sub -> sub -> sub
    val umulh : Type.imm -> sub -> sub -> sub
    val urem : Type.imm -> sub -> sub -> sub
    val and_ : Type.imm -> sub -> sub -> sub
    val or_ : Type.imm -> sub -> sub -> sub
    val asr_ : Type.imm -> sub -> sub -> sub
    val lsl_ : Type.imm -> sub -> sub -> sub
    val lsr_ : Type.imm -> sub -> sub -> sub
    val rol : Type.imm -> sub -> sub -> sub
    val ror : Type.imm -> sub -> sub -> sub
    val xor : Type.imm -> sub -> sub -> sub

    (** Comparison operators. *)

    val eq : Type.basic -> sub -> sub -> sub
    val ge : Type.basic -> sub -> sub -> sub
    val gt : Type.basic -> sub -> sub -> sub
    val ne : Type.basic -> sub -> sub -> sub
    val le : Type.basic -> sub -> sub -> sub
    val lt : Type.basic -> sub -> sub -> sub
    val o : Type.fp -> sub -> sub -> sub
    val sge : Type.imm -> sub -> sub -> sub
    val sgt : Type.imm -> sub -> sub -> sub
    val sle : Type.imm -> sub -> sub -> sub
    val slt : Type.imm -> sub -> sub -> sub
    val uo : Type.fp -> sub -> sub -> sub

    (** Unary operators. *)

    val neg : Type.basic -> sub -> sub
    val not_ : Type.imm -> sub -> sub
    val clz : Type.imm -> sub -> sub
    val ctz : Type.imm -> sub -> sub
    val popcnt : Type.imm -> sub -> sub

    (** Cast operators. *)

    val fext : Type.fp -> sub -> sub
    val fibits : Type.fp -> sub -> sub
    val flag : Type.imm -> sub -> sub
    val ftosi : Type.fp -> Type.imm -> sub -> sub
    val ftoui : Type.fp -> Type.imm -> sub -> sub
    val ftrunc : Type.fp -> sub -> sub
    val ifbits : Type.imm_base -> sub -> sub
    val itrunc : Type.imm -> sub -> sub
    val sext : Type.imm -> sub -> sub
    val sitof : Type.imm -> Type.fp -> sub -> sub
    val uitof : Type.imm -> Type.fp -> sub -> sub
    val zext : Type.imm -> sub -> sub
  end
end

module Subst : sig
  (** A substitition. *)
  type 'r t = private 'r Isel_internal.Subst.t

  (** Lookup a register with a basic type. *)
  val regvar : 'r t -> string -> ('r * Type.basic) option

  (** Lookup a register with a vector type. *)
  val regvar_v : 'r t -> string -> 'r option

  (** Lookup an integer constant. *)
  val imm : 'r t -> string -> (Bv.t * Type.imm) option

  (** Lookup a 32-bit float constant. *)
  val single : 'r t -> string -> Float32.t option

  (** Lookup a 64-bit float constant. *)
  val double : 'r t -> string -> float option

  (** Lookup a symbol. *)
  val sym : 'r t -> string -> (string * int) option

  (** Lookup a program label. *)
  val label : 'r t -> string -> Label.t option

  (** Lookup a boolean constant. *)
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
  val (=>) : Pattern.toplevel -> ('r, 'i) callback -> ('r, 'i) t

  (** Same as [=>], but accepts multiple callbacks for matching the same pattern.

      The callbacks are invoked in the order that they are provided, until one
      of them produces a successful match.
  *)
  val (=>*) : Pattern.toplevel -> ('r, 'i) callback list -> ('r, 'i) t

  val (let*!) : 'a option -> ('a -> 'b option C.t) -> 'b option C.t
  val (!!!) : 'a -> 'a option C.t
  val guard : bool -> unit option
end
