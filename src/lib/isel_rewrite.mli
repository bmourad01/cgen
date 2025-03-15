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
    (** {1} Toplevel instructions. *)

    (** [store t x y]: store value [x] of type [t] to address [y]. *)
    val store : [Type.basic | `v128] -> sub -> sub -> toplevel

    (** [br c y n]: branch on condition [c] to [y] if true, and [n] if false. *)
    val br : sub -> sub -> sub -> toplevel

    (** [call x]: call to function [x]. *)
    val call : sub -> toplevel

    (** [hlt]: halt the program. *)
    val hlt : toplevel

    (** [jmp x]: jump to location [x]. *)
    val jmp : sub -> toplevel

    (** [ret]: return from the function. *)
    val ret : toplevel

    (** [move x y]: move value [y] into destination [x].

        [x] is never a memory location, see [store] for such semantics.
    *)
    val move : sub -> sub -> toplevel

    (** [sw ty idx tbl] denotes a jump table with [idx] being the
        index into the table, and [tbl] being the table descriptor
        itself (see [Subst.table]). *)
    val sw : Type.imm -> sub -> sub -> toplevel

    (** {1} Constants. *)

    (** [bool b]: a constant boolean value [b]. *)
    val bool : bool -> sub

    (** [double d]: a constant double-precision floating point value [d]. *)
    val double : float -> sub

    (** [int i t]: a constant bitvector [i] of type [t]. *)
    val int : Bv.t -> Type.imm -> sub

    (** [int8 i]: a constant 8-bit integer [i] modulo [256]. *)
    val i8 : int -> sub

    (** [int16 i]: a constant 16-bit integer [i] modulo [65535]. *)
    val i16 : int -> sub

    (** [int32 i]: a constant 32-bit integer. *)
    val i32 : int32 -> sub

    (** [int64 i]: a constant 64-bit integer. *)
    val i64 : int64 -> sub

    (** [single s]: a constant single-precision floating point value [s]. *)
    val single : Float32.t -> sub

    (** [sym s o]: a constant symbol [s] at offset [o]. *)
    val sym : string -> int -> sub

    (** {1} Loads. *)

    (** [load t x]: load a value of type [t] from address [x]. *)
    val load : Type.basic -> sub -> sub

    (** {1} Conditional selection. *)

    (** [sel t c y n]: select either [y] or [n] of type [t], depending on
        the value of condition [c]. *)
    val sel : Type.basic -> sub -> sub -> sub -> sub

    (** {1} Binary operators. *)

    (** [add t x y]: adds [x] and [y] of type [t]. *)
    val add : Type.basic -> sub -> sub -> sub

    (** [div t x y]: divides [x] by [y] of type [t].

        For integer types, this operation is signed. See [udiv] for the
        unsigned version.
    *)
    val div : Type.basic -> sub -> sub -> sub

    (** [mul t x y]: multiplies [x] and [y] of type [t]. *)
    val mul : Type.basic -> sub -> sub -> sub

    (** [mulh t x y]: signed multiplication of the integer values [x]
        and [y] of type [t], and returns the upper half. *)
    val mulh : Type.imm -> sub -> sub -> sub

    (** [rem t x y]: signed integer remainder of [x] by [y] of type [t]. *)
    val rem : Type.imm -> sub -> sub -> sub

    (** [sub t x y]: subtract [x] by [y] of type [t]. *)
    val sub : Type.basic -> sub -> sub -> sub

    (** [udiv t x y]: unsigned division of integer [x] by [y] of type [t]. *)
    val udiv : Type.imm -> sub -> sub -> sub

    (** [umulh t x y]: unsigned multiplication of the integer values [x]
        and [y] of type [t], and returns the upper half. *)
    val umulh : Type.imm -> sub -> sub -> sub

    (** [urem t x y]: unsigned integer remainder of [x] by [y] of type [t]. *)
    val urem : Type.imm -> sub -> sub -> sub

    (** [and_ t x y]: bitwise AND of integers [x] and [y] of type [t]. *)
    val and_ : Type.imm -> sub -> sub -> sub

    (** [or_ t x y]: bitwise OR of integers [x] and [y] of type [t]. *)
    val or_ : Type.imm -> sub -> sub -> sub

    (** [asr_ t x y]: arithmetic shift right of [x] by [y] bits of type [t]. *)
    val asr_ : Type.imm -> sub -> sub -> sub

    (** [lsl_ t x y]: logical shift left of [x] by [y] bits of type [t]. *)
    val lsl_ : Type.imm -> sub -> sub -> sub

    (** [lsr_ t x y]: logical shift right of [x] by [y] bits of type [t]. *)
    val lsr_ : Type.imm -> sub -> sub -> sub

    (** [rol t x y]: rotate [x] left by [y] bits of type [t]. *)
    val rol : Type.imm -> sub -> sub -> sub

    (** [ror t x y]: rotate [x] right by [y] bits of type [t].  *)
    val ror : Type.imm -> sub -> sub -> sub

    (** [xor t x y]: exclusive OR of [x] and [y] of type [t]. *)
    val xor : Type.imm -> sub -> sub -> sub

    (** {6} Comparison operators. *)

    (** [eq t x y]: equality condition for [x] and [y] of type [t]. *)
    val eq : Type.basic -> sub -> sub -> sub

    (** [ge t x y]: condition where [x] is greater than or equal to [y]
        of type [t].

        For integer types, this operation is unsigned, See [sge] for the
        signed version.
    *)
    val ge : Type.basic -> sub -> sub -> sub

    (** [gt t x y]: condition where [x] is greater than [y] of type [t].

        For integer types, this operation is unsigned, See [sgt] for the
        signed version.
    *)
    val gt : Type.basic -> sub -> sub -> sub

    (** [ne t x y]: inequality condition for [x] and [y] of type [t]. *)
    val ne : Type.basic -> sub -> sub -> sub

    (** [le t x y]: condition whre [x] is less than or equal to [y] of
        type [t].

        For integer types, this operation is unsigned. See [sle] for the
        signed version.
    *)
    val le : Type.basic -> sub -> sub -> sub

    (** [lt t x y]: condition whre [x] is less than [y] of  type [t].

        For integer types, this operation is unsigned. See [slt] for the
        signed version.
    *)
    val lt : Type.basic -> sub -> sub -> sub

    (** [o t x y]: condition where the comparison of floating point terms
        [x] and [y] of type [t] is ordered. *)
    val o : Type.fp -> sub -> sub -> sub

    (** [sge t x y]: signed comparison where integer [x] is greater than or
        equal to [y] of type [t]. *)
    val sge : Type.imm -> sub -> sub -> sub

    (** [sgt t x y]: signed comparison where integer [x] is greater than [y]
        of type [t]. *)
    val sgt : Type.imm -> sub -> sub -> sub

    (** [sle t x y]: signed comparison where integer [x] is less than or
        equal to [y] of type [t]. *)
    val sle : Type.imm -> sub -> sub -> sub

    (** [slt t x y]: signed comparison where integer [x] is less than [y]
        of type [t]. *)
    val slt : Type.imm -> sub -> sub -> sub

    (** [uo t x y]: condition where the comparison of floating point terms
        [x] and [y] of type [t] is unordered. *)
    val uo : Type.fp -> sub -> sub -> sub

    (** {1} Unary operators. *)

    (** [neg t x]: negate the term [x] of type [t]. *)
    val neg : Type.basic -> sub -> sub

    (** [not_ t x]: bitwise NOT of the integer [x] of type [t]. *)
    val not_ : Type.imm -> sub -> sub

    (** [clz t x]: count the leading zeroes of integer [x], returning a value
        of type [t]. *)
    val clz : Type.imm -> sub -> sub

    (** [ctz t x]: count the trailing zeroes of integer [x], returning a value
        of type [t]. *)
    val ctz : Type.imm -> sub -> sub

    (** [popcnt t x]: count the number of set bits of integer [x], returning a
        value of of type [t]. *)
    val popcnt : Type.imm -> sub -> sub

    (** {1} Cast operators. *)

    (** [fext t x]: extend the floating point value [x] to type [t]. *)
    val fext : Type.fp -> sub -> sub

    (** [fibits t x]: return a floating point value of type [t] from the underlying
        bit representation of integer value [x]. *)
    val fibits : Type.fp -> sub -> sub

    (** [flag t x]: extend a condition (boolean) value [x] to an integer of type [t]. *)
    val flag : Type.imm -> sub -> sub

    (** [ftosi f i x]: convert a floating point value [x] of type [f] to a signed
        integer of type [i]. *)
    val ftosi : Type.fp -> Type.imm -> sub -> sub

    (** [ftoui f i x]: convert a floating point value [x] of type [f] to an unsigned
        integer of type [i]. *)
    val ftoui : Type.fp -> Type.imm -> sub -> sub

    (** [ftrunc f x]: truncate a floating point value [x] to type [t]. *)
    val ftrunc : Type.fp -> sub -> sub

    (** [ifbits t x]: return and integer value of type [t] from the underlying bit
        representation of floating point value [x]. *)
    val ifbits : Type.imm_base -> sub -> sub

    (** [itrunc t x]: truncate the integer value [x] to type [t]. *)
    val itrunc : Type.imm -> sub -> sub

    (** [sext t x]: sign-extend the integer value [x] to type [t]. *)
    val sext : Type.imm -> sub -> sub

    (** [sitof i f x]: convert a floating point value [x] of type [f] to a signed
        integer value of type [i]. *)
    val sitof : Type.imm -> Type.fp -> sub -> sub

    (** [uitof i f x]: convert a floating point value [x] of type [f] to an unsigned
        integer value of type [i]. *)
    val uitof : Type.imm -> Type.fp -> sub -> sub

    (** [zext t x]: zero-extend the integer value [x] to type [t]. *)
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

  (** Lookup a switch table (including the default label).

      The table is sorted from lowest to highest.
  *)
  val table : 'r t -> string -> (Label.t * (Bv.t * Label.t) list) option
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

  (** Lifts an [option] computation into the monad and binds it to a result. *)
  val (let*!) : 'a option -> ('a -> 'b option C.t) -> 'b option C.t

  (** [!!!a] is equivalent to [C.return (Some a)] *)
  val (!!!) : 'a -> 'a option C.t

  (** [guard b] returns [Some ()] if [b] is [true], and [None] otherwise. *)
  val guard : bool -> unit option

  (** [try_ x fs] attempts to apply the functions in [fs] to [x] from left
      to right. *)
  val try_ : 'a -> ('a -> 'b option C.t) list -> 'b option C.t
end
