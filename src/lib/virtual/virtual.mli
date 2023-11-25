(** The virtual, target-agnostic machine, represented as a
    control-flow graph (CFG).

    It is used as the entry-level IR for the pipeline, to
    perform transformations that are not target-specific.
*)

open Core
open Graphlib.Std
open Regular.Std

(** A constant value.

    [`bool f] is a truth value.

    [`int (n, t)] is a constant integer value of size [t].

    [`float f] is a single-precision floating-point value.

    [`double d] is a double-precision floating-point value.

    [`sym (s, n)] is a reference to a global symbol [s], with a
    constant offset [n].
*)
type const = [
  | `bool   of bool
  | `int    of Bv.t * Type.imm
  | `float  of Float32.t
  | `double of float
  | `sym    of string * int
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pretty-prints a constant value. *)
val pp_const : Format.formatter -> const -> unit

(** An operand to an instruction. *)
type operand = [
  | const
  | `var of Var.t
] [@@deriving bin_io, compare, equal, hash, sexp]

(** [var_of_operand a] returns [Some x] if [a] is a variable [x]. *)
val var_of_operand : operand -> Var.t option

(** Pretty-prints an argument to an instruction. *)
val pp_operand : Format.formatter -> operand -> unit

(** Inter-function destination.

    [`addr a] is a static absolute addrsss.

    [`sym (s, o)] is a global symbol [s] plus an offset [o].

    [`var v] is a dynamic absolute address.
*)
type global = [
  | `addr of Bv.t
  | `sym  of string * int
  | `var  of Var.t
] [@@deriving bin_io, compare, equal, sexp]

(** [var_of_global g] returns [Some x] if [g] is a variable [x]. *)
val var_of_global : global -> Var.t option

(** Pretty-prints the global destination. *)
val pp_global : Format.formatter -> global -> unit

(** Intra-function destination.

    [`label (l, args)] is the label [l] of a block in the current
    function, with a list of operands [args].
*)
type local = [
  | `label of Label.t * operand list
] [@@deriving bin_io, compare, equal, sexp]

(** Returns the free variables in the local destination. *)
val free_vars_of_local : local -> Var.Set.t

(** Pretty-prints the local destination. *)
val pp_local : Format.formatter -> local -> unit

(** The destination for a control flow transfer. *)
type dst = [
  | global
  | local
] [@@deriving bin_io, compare, equal, sexp]

(** Returns the free variables in the destination. *)
val free_vars_of_dst : dst -> Var.Set.t

(** Pretty-prints a control-flow destination. *)
val pp_dst : Format.formatter -> dst -> unit

(** Data-flow-effectful instruction. *)
module Insn : sig
  (** Arithmetic binary operations.

      [`add t]: addition.

      [`div t]: division.

      [`mul t]: multiplication.

      [`mulh t]: signed immediate high multiplication.

      [`rem t]: remainder.

      [`sub t]: subtraction.

      [`udiv t]: unsigned division (immediate only).

      [`umulh t]: unsigned immediate high multiplication.

      [`urem t]: unsigned remainder (immediate only).
  *)
  type arith_binop = [
    | `add   of Type.basic
    | `div   of Type.basic
    | `mul   of Type.basic
    | `mulh  of Type.imm
    | `rem   of Type.basic
    | `sub   of Type.basic
    | `udiv  of Type.imm
    | `umulh of Type.imm
    | `urem  of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the arithmetic binary operator. *)
  val pp_arith_binop : Format.formatter -> arith_binop -> unit

  (** Arithmetic unary operations.

      [`neg t]: negation.
  *)
  type arith_unop = [
    | `neg of Type.basic
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the arithmetic unary operator. *)
  val pp_arith_unop : Format.formatter -> arith_unop -> unit

  (** Bitwise binary operations.

      [`and_ t]: bitwise intersection (AND).

      [`or_ t]: bitwise union (OR).

      [`asr_ t]: arithmetic shift right.

      [`lsl_ t]: logical shift left.

      [`lsr_ t]: logical shift right.

      [`rol t]: rotate left.

      [`ror t]: rotate right.

      [`xor t]: bitwise difference (exclusive-OR).
  *)
  type bitwise_binop = [
    | `and_ of Type.imm
    | `or_  of Type.imm
    | `asr_ of Type.imm
    | `lsl_ of Type.imm
    | `lsr_ of Type.imm
    | `rol  of Type.imm
    | `ror  of Type.imm
    | `xor  of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the bitwise binary operator. *)
  val pp_bitwise_binop : Format.formatter -> bitwise_binop -> unit

  (** Bitwise unary operations.

      [`clz t]: count leading zeroes.

      [`ctz t]: count trailing zeroes.

      [`not_ t]: bitwise complement (NOT).

      [`popcnt t]: population count (number of set bits).
  *)
  type bitwise_unop = [
    | `clz    of Type.imm
    | `ctz    of Type.imm
    | `not_   of Type.imm
    | `popcnt of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the bitwise unary operator. *)
  val pp_bitwise_unop : Format.formatter -> bitwise_unop -> unit

  (** Comparison operations.

      [`eq t l, r)]: equal.

      [`ge t]: greater or equal.

      [`gt t]: greater than.

      [`le t]: less or equal.

      [`lt t]: less than.

      [`ne t]: not equal.

      [`o t]: ordered (floating point only).

      [`sge t]: signed greater or equal (immediate only).

      [`sgt t]: signed greater than (immediate only).

      [`sle t]: signed less or equal (immediate only).

      [`slt t]: signed less than (immediate only).

      [`uo t]: unordered (floating point only).
  *)
  type cmp = [
    | `eq  of Type.basic
    | `ge  of Type.basic
    | `gt  of Type.basic
    | `le  of Type.basic
    | `lt  of Type.basic
    | `ne  of Type.basic
    | `o   of Type.fp
    | `sge of Type.imm
    | `sgt of Type.imm
    | `sle of Type.imm
    | `slt of Type.imm
    | `uo  of Type.fp
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints a comparison operation. *)
  val pp_cmp : Format.formatter -> cmp -> unit

  (** Cast operations.

      [`fext t]: extends a floating point value to a higher
      precision.

      [`fibits t]: reinterpret the bits of an integer as a
      float of type [t].

      [`flag t]: converts a flag bit into an integer of type [t].

      [`ftosi (t, i)]: cast a float of type [t] to a signed
      integer of type [i].

      [`ftoui (t, i)]: cast a float of type [t] to an unsigned
      integer of type [i].

      [`ftrunc t]: truncate a float to a float of type [t].

      [`ifbits t]: reinterpret the bits of a floating point
      number as an integer of type [t].

      [`itrunc t]: truncate an integer to an integer of type [t].

      [`sext t]: sign-extend an integer to an integer of type [t].

      [`sitof (t, f)]: cast a signed integer of type [t] to a float
      of type [f].

      [`uitof (t, f)]: cast an unsigned integer of type [t] to a
      float of type [f].

      [`zext t]: zero-extend an integer to an integer of type [t].
  *)
  type cast = [
    | `fext   of Type.fp
    | `fibits of Type.fp
    | `flag   of Type.imm
    | `ftosi  of Type.fp * Type.imm
    | `ftoui  of Type.fp * Type.imm
    | `ftrunc of Type.fp
    | `ifbits of Type.imm_base
    | `itrunc of Type.imm
    | `sext   of Type.imm
    | `sitof  of Type.imm * Type.fp
    | `uitof  of Type.imm * Type.fp
    | `zext   of Type.imm
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints a cast operation. *)
  val pp_cast : Format.formatter -> cast -> unit 

  (** Copy operations.

      [`copy t]: move to a destination of type [t].

      [`ref]: copy a reference to a compound type.

      [`unref s]: reinterpret a reference as a compound type [s],
      mainly for passing as an argument to a function.
  *)
  type copy = [
    | `copy  of Type.basic
    | `ref
    | `unref of string
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints a copy operation. *)
  val pp_copy : Format.formatter -> copy -> unit

  (** All binary operations. *)
  type binop = [
    | arith_binop
    | bitwise_binop
    | cmp
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the binary operator. *)
  val pp_binop : Format.formatter -> binop -> unit

  (** All unary operations. *)
  type unop = [
    | arith_unop
    | bitwise_unop
    | cast
    | copy
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  (** Pretty-prints the unary operator. *)
  val pp_unop : Format.formatter -> unop -> unit

  (** All basic instructions.

      [`bop (x, b, l, r)]: compute [b(l, r)] and store the result in [x].

      [`uop (x, u, a)]: compute [u(a)] and store the result in [x].

      [`sel (x, t, c, l, r)]: evaluate [c]; if non-zero then select [l]
      and assign to [x], otherwise select [r]. Both [l] and [r] must have
      type [t].
  *)
  type basic = [
    | `bop of Var.t * binop * operand * operand
    | `uop of Var.t * unop  * operand
    | `sel of Var.t * Type.basic * Var.t * operand * operand
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the basic instruction. *)
  val free_vars_of_basic : basic -> Var.Set.t

  (** Pretty-prints a basic instruction. *)
  val pp_basic : Format.formatter -> basic -> unit

  (** A call instruction.

      [`call (a, f, args, vargs)]: call to [f] with arguments [args] and
      [vargs], where [vargs] is the list of variadic arguments. If [a]
      is [Some (x, t)], then the function returns a value of type [t],
      which is assigned to variable [x].

      Note that variadic calls require at least one non-variadic argument.
  *)
  type call = [
    | `call of (Var.t * Type.arg) option * global * operand list * operand list
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the call. *)
  val free_vars_of_call : call -> Var.Set.t

  (** Returns [true] if the call is variadic. *)
  val is_variadic : call -> bool

  (** Pretty-prints a call instruction. *)
  val pp_call : Format.formatter -> call -> unit

  (** Memory operations.

      [`load (x, t, a)]: load a value of type [t] from address [a] and
      assign the result to [x].

      [`store (t, v, a)]: store a value [v] of type [t] to address [a].
  *)
  type mem = [
    | `load  of Var.t * Type.basic * operand
    | `store of Type.basic * operand * operand
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the memory operation. *)
  val free_vars_of_mem : mem -> Var.Set.t

  (** Pretty-prints a memory operation. *)
  val pp_mem : Format.formatter -> mem -> unit

  (** Variadic argument list pointer. *)
  type alist = global [@@deriving bin_io, compare, equal, sexp]

  val pp_alist : Format.formatter -> alist -> unit

  (** A variadic argument instruction.

      [`vastart x] initializes [x] with a pointer to the start of the
      variadic argument list for the current function.

      [`vaarg (x, t, y)] fetches the next element of type [t] from the
      variadic argument list [y], and assigns it to [x].
  *)
  type variadic = [
    | `vastart of alist
    | `vaarg   of Var.t * Type.arg * alist
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the variadic argument
      instruction. *)
  val free_vars_of_variadic : variadic -> Var.Set.t

  (** Pretty-prints a variadic argument instruction. *)
  val pp_variadic : Format.formatter -> variadic -> unit

  (** A data operation. *)
  type op = [
    | basic
    | call
    | mem
    | variadic
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the assigned variable of the operation, if it exists. *)
  val lhs_of_op : op -> Var.t option

  (** [has_lhs d x] returns [true] if the instruction [d] assigns the
      variable [x]. *)
  val op_has_lhs : op -> Var.t -> bool

  (** Returns the set of free variables in the data instruction. *)
  val free_vars_of_op : op -> Var.Set.t

  (** Pretty-prints a data operation. *)
  val pp_op : Format.formatter -> op -> unit

  (** Tags for various information about the instruction. *)
  module Tag : sig
    (** Do not attempt to transform this call into a tail call. *)
    val non_tail : unit Dict.tag
  end

  (** A labeled data operation. *)
  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a labeled instruction. *)
  val create : ?dict:Dict.t -> op -> label:Label.t -> t

  (** The label of the instruction. *)
  val label : t -> Label.t

  (** The operation itself. *)
  val op : t -> op

  (** Replaces the operation *)
  val with_op : t -> op -> t

  (** Returns the dictionary of the instruction. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the instruction. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag i t v] binds [v] to tag [t] in the dictionary of [i]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the instruction has a given label. *)
  val has_label : t -> Label.t -> bool

  (** Same as [free_vars_of_op (op i)]. *)
  val free_vars : t -> Var.Set.t

  (** Same as [lhs_of_op (op i)]. *)
  val lhs : t -> Var.t option

  (** Same as [op_has_lhs (op i)]. *)
  val has_lhs : t -> Var.t -> bool

  (** Returns [true] for instructions that have side effects. *)
  val is_effectful_op : op -> bool

  (** Returns [true] for instructions that can store to memory. *)
  val can_store_op : op -> bool

  (** Returns [true] for instructions that can load from memory. *)
  val can_load_op : op -> bool

  (** Same as [is_effectful_op (op i)]. *)
  val is_effectful : t -> bool

  (** Same as [can_store_op (op i)]. *)
  val can_store : t -> bool

  (** Same as [can_load_op (op i)]. *)
  val can_load : t -> bool

  (** Transforms the underlying operation. *)
  val map : t -> f:(op -> op) -> t

  (** Same as [pp_op]. *)
  val pp : Format.formatter -> t -> unit
end

type insn = Insn.t [@@deriving bin_io, compare, equal, sexp]

(** Evaluation of instructions. *)
module Eval : sig
  (** [binop_int o x y] evaluates a binary operator [o] over integers
      [x] and [y], and returns the result if it is defined. *)
  val binop_int :
    Insn.binop ->
    Bv.t ->
    Bv.t ->
    [`bool of bool | `int of Bv.t * Type.imm] option

  (** [binop_single o x y] evaluates a binary operator [o] over 32-bit
      floats [x] and [y], and returns the result if it is defined. *)
  val binop_single :
    Insn.binop ->
    Float32.t ->
    Float32.t ->
    [`bool of bool | `float of Float32.t] option

  (** [binop_double o x y] evaluates a binary operator [o] over 64-bit
      floats [x] and [y], and returns the result if it is defined. *)
  val binop_double :
    Insn.binop ->
    float ->
    float ->
    [`bool of bool | `double of float] option

  (** [unop_int o x ty] evaluates a unary operator [o] over the integer
      [x] with type [ty], and returns the result if it is defined. *)
  val unop_int :
    Insn.unop ->
    Bv.t ->
    Type.imm ->
    [`double of float | `float of Float32.t | `int of Bv.t * Type.imm] option

  (** [unop_single o x] evaluates a unary operator [o] over the 32-bit float
      [x], and returns the result if it is defined. *)
  val unop_single :
    Insn.unop ->
    Float32.t ->
    [`double of float | `float of Float32.t | `int of Bv.t * Type.imm] option

  (** [unop_double o x] evaluates a unary operator [o] over the 64-bit float
      [x], and returns the result if it is defined. *)
  val unop_double :
    Insn.unop ->
    float ->
    [`double of float | `int of Bv.t * Type.imm] option
end

(** Control-flow-effectful instructions. *)
module Ctrl : sig
  (** A switch table. *)
  module Table : sig
    type t [@@deriving bin_io, compare, equal, sexp]

    (** Creates a switch table from an association list.

        @raise Invalid_argument if the list has duplicate keys.
    *)
    val create_exn : (Bv.t * local) list -> Type.imm -> t

    (** Same as [create_exn], but returns an error upon failure. *)
    val create : (Bv.t * local) list -> Type.imm -> t Or_error.t

    (** Returns the elements of the table. *)
    val enum : t -> (Bv.t * local) seq

    (** Returns the number of cases in the table. *)
    val length : t -> int

    (** Returns the immediate type for the index into the table. *)
    val typ : t -> Type.imm

    (** [find t v] searches the table [t] for the label associated
        with the constant [v]. *)
    val find : t -> Bv.t -> local option

    (** [map_exn t ~f] applies [f] to each element of [t].

        @raise Invalid_argument if [f] produces a duplicate key.
    *)
    val map_exn : t -> f:(Bv.t -> local -> Bv.t * local) -> t

    (** Returns the set of free variables in the table. *)
    val free_vars : t -> Var.Set.t

    (** Same as [map_exn], but returns [Error _] if [f] produces a
        duplicate key. *)
    val map : t -> f:(Bv.t -> local -> Bv.t * local) -> t Or_error.t
  end

  type table = Table.t [@@deriving bin_io, compare, equal, sexp]

  (** A valid index into the switch table.

      The [`sym (s, offset)] constructor is included because it is
      technically legal to use a symbol as an index into the table.
      A constant propagation pass could resolve the index to some
      symbol, although this is rarely a case.
  *)
  type swindex = [
    | `var of Var.t
    | `sym of string * int
  ] [@@deriving bin_io, compare, equal, sexp]

  (** A control-flow instruction.

      [`hlt] terminates execution of the program. This is typically used
      to mark certain program locations as unreachable.

      [`jmp dst] is an unconditional jump to the destination [dst].

      [`br (cond, yes, no)] evaluates [cond] and jumps to [yes] if it
      is non-zero. Otherwise, the destination is [no].

      [`ret x] returns from a function. If the function returns a value,
      then [x] holds the value (and must not be [None]).

      [`sw (typ, index, default, table)] implements a jump table.
      For a variable [index] of type [typ], it will find the associated
      label of [index] in [table] and jump to it, if it exists. If not,
      then the destination of the jump is [default].
  *)
  type t = [
    | `hlt
    | `jmp   of dst
    | `br    of Var.t * dst * dst
    | `ret   of operand option
    | `sw    of Type.imm * swindex * local * table
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the control-flow instruction. *)
  val free_vars : t -> Var.Set.t

  (** Pretty-prints a control-flow instruction. *)
  val pp : Format.formatter -> t -> unit
end

type ctrl = Ctrl.t [@@deriving bin_io, compare, equal, sexp]

(** A control-flow edge. *)
module Edge : sig
  (** The kinds of edges that may occur:

      [`always]: unconditional jump.

      [`true_ x]: taken if [x] is non-zero.

      [`false_ x]: taken if [x] is zero.

      [`switch_ (x, vs, def)]: taken if [x \in vs]. If [def] is [true], then
      the edge also applies to the default case.

      [`default x]: taken if [x] doesn't match any entry in the switch table.
  *)
  type t = [
    | `always
    | `true_ of Var.t
    | `false_ of Var.t
    | `switch of Ctrl.swindex * Bv.t list * bool
    | `default of Ctrl.swindex
  ] [@@deriving bin_io, compare, equal, sexp]

  include Regular.S with type t := t
end

type edge = Edge.t [@@deriving bin_io, compare, equal, sexp]

(** A basic block. *)
module Blk : sig
  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a basic block. *)
  val create :
    ?dict:Dict.t ->
    ?args:Var.t list ->
    ?insns:insn list ->
    label:Label.t ->
    ctrl:ctrl ->
    unit ->
    t

  (** Returns the label of the basic block. *)
  val label : t -> Label.t

  (** Returns the arguments of the basic block. *)
  val args : ?rev:bool -> t -> Var.t seq

  (** Returns the sequence of data instructions. *)
  val insns : ?rev:bool -> t -> insn seq

  (** Returns the control-flow instruction (also called the terminator)
      of the block. *)
  val ctrl : t -> ctrl

  (** Returns the dictionary of the block. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the block. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag b t v] binds [v] to tag [t] in the dictionary of [b]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** [has_label b l] returns [true] if block [b] has label [l]. *)
  val has_label : t -> Label.t -> bool

  (** Returns a mapping from instruction labels to instructions.

      @raise Invalid_argument if there are duplicate labels
  *)
  val map_of_insns : t -> insn Label.Tree.t

  (** Returns the live-out mappings for each instruction and the set
      of free variables in the block. *)
  val liveness : t -> Var.Set.t Label.Tree.t * Var.Set.t

  (** Equivalent to [snd (liveness blk)]. *)
  val free_vars : t -> Var.Set.t

  (** [uses_var b x] returns [true] if the variable [x] appears in the
      free variables of [b].

      Equivalent to [Set.mem (free_vars b) x].
  *)
  val uses_var : t -> Var.t -> bool

  (** [defines_var b x] returns [true] if the variable [x] is defined
      in the block [b]. *)
  val defines_var : t -> Var.t -> bool

  (** Returns [true] if the block has a data instruction associated with
      the label. *)
  val has_insn : t -> Label.t -> bool

  (** Finds the data instruction with the associated label. *)
  val find_insn : t -> Label.t -> insn option

  (** Returns the next data instruction (after the given label) if it
      exists. *)
  val next_insn : t -> Label.t -> insn option

  (** Returns the previous data instruction (before the given label) if it
      exists. *)
  val prev_insn : t -> Label.t -> insn option

  (** Applies [f] to each argument of the block. *)
  val map_args : t -> f:(Var.t -> Var.t) -> t

  (** [map_insns b ~f] returns [b] with each data instruction applied
      to [f]. *)
  val map_insns : t -> f:(Label.t -> Insn.op -> Insn.op) -> t

  (** [map_ctrl b ~f] returns [b] with the terminator applied to [f]. *)
  val map_ctrl : t -> f:(ctrl -> ctrl) -> t

  (** [prepend_arg b a ?before] prepends the argument [a] to the block

      If [before] is [None], then [a] is inserted at the beginning of
      the argument list.

      If [before] is [Some x], then [a] will appear directly before the
      argument [x]. If [x] doesn't exist, then [a] is not inserted.
  *)
  val prepend_arg : ?before:Var.t option -> t -> Var.t -> t

  (** [append_arg b a ?after] appends the argument [a] to the block [b].

      If [after] is [None], then [a] is inserted at the end of the
      argument list.

      If [after] is [Some x], then [a] will appear directly after the
      argument [x]. If [x] doesn't exist, then [a] is not inserted.
  *)
  val append_arg : ?after:Var.t option -> t -> Var.t -> t

  (** [prepend_insn b d ?before] prepends the data instruction [d] to
      the block [b].

      If [before] is [None], then [d] is inserted at the beginning of
      the data instructions.

      If [before] is [Some l], then [d] will appear directly before the
      data instruction at label [l]. If [l] doesn't exist, then [d] is
      not inserted.
  *)
  val prepend_insn : ?before:Label.t option -> t -> insn -> t

  (** [append_insn b d ?after] appends the data instruction [d] to
      the block [b].

      If [after] is [None], then [d] is inserted at the end of the
      data instructions.

      If [after] is [Some l], then [d] will appear directly after the
      data instruction at label [l]. If [l] doesn't exist, then [d] is
      not inserted.
  *)
  val append_insn : ?after:Label.t option -> t -> insn -> t

  (** Similar to [prepend_insn], but for a list of instructions.

      Note that the instructions are prepended to [before] starting
      with the last instruction.
  *)
  val prepend_insns : ?before:Label.t option -> t -> insn list -> t

  (** Similar to [append_insn], but for a list of instructions.

      Note that the instructions are appended to [after] starting
      with the first instruction.
  *)
  val append_insns : ?after:Label.t option -> t -> insn list -> t

  (** Replaces the control-flow instruction in the block. *)
  val with_ctrl : t -> ctrl -> t

  (** Replaces the instructions of the block. *)
  val with_insns : t -> insn list -> t

  (** [remove_arg b x] removes an argument [x] from the block [b],
      if it exists. *)
  val remove_arg : t -> Var.t -> t

  (** [remove_insn b l] removes a data instruction with label [l] from
      the block [b], if it exists. *)
  val remove_insn : t -> Label.t -> t

  (** [has_arg b x] returns true if [b] has an argument [x]. *)
  val has_arg : t -> Var.t -> bool

  (** [has_lhs b x] returns [true] if a data instruction in [b] defines
      [x]. *)
  val has_lhs : t -> Var.t -> bool

  include Regular.S with type t := t
end

type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]

(** A function. *)
module Func : sig
  (** A stack slot. *)
  module Slot : sig
    type t [@@deriving bin_io, compare, equal, sexp]

    (** [create_exn x ~size ~align] creates a slot for variable [x] with
        [size] and [align].

        @raise Invalid_argument if [size < 1], [align < 1], or [align] is
        not a power of two.
    *)
    val create_exn : Var.t -> size:int -> align:int -> t

    (** Same as [create_exn], but returns an error instead of raising. *)
    val create : Var.t -> size:int -> align:int -> t Or_error.t

    (** The variable associated with the slot. *)
    val var : t -> Var.t

    (** The size of the slot in bytes. *)
    val size : t -> int

    (** The alignment of the slot in bytes. *)
    val align : t -> int

    (** [is_var s x] returns [true] if slot [s] is associated with the
        variable [x]. *)
    val is_var : t -> Var.t -> bool

    val pp : Format.formatter -> t -> unit
  end

  type slot = Slot.t [@@deriving bin_io, compare, equal, sexp]

  val pp_slot : Format.formatter -> slot -> unit

  (** Tags for various information about the function. *)
  module Tag : sig
    (** The return type of the function. *)
    val return : Type.arg Dict.tag

    (** Indicates whether the function is variadic or not. *)
    val variadic : unit Dict.tag

    (** Indicates whether the function should be interpreted
        as not returning. *)
    val noreturn : unit Dict.tag

    (** The linkage of the function. *)
    val linkage : Linkage.t Dict.tag
  end

  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a function.

      It is assumed that [blks] is ordered such that the entry block is
      the first element.

      The entry block must have no incoming control-flow edges (this is
      enforced in [Typecheck]).

      @raise Invalid_argument if [blks] is empty.
  *)
  val create_exn :
    ?dict:Dict.t ->
    ?slots:slot list ->
    name:string ->
    blks:blk list ->
    args:(Var.t * Type.arg) list ->
    unit ->
    t

  (** Same as [create_exn], but returns an error upon failure. *)
  val create :
    ?dict:Dict.t ->
    ?slots:slot list ->
    name:string ->
    blks:blk list ->
    args:(Var.t * Type.arg) list ->
    unit ->
    t Or_error.t

  (** Returns the name of the function. *)
  val name : t -> string

  (** Returns the slots of the function. *)
  val slots : ?rev:bool -> t -> slot seq

  (** Returns the basic blocks of the function. *)
  val blks : ?rev:bool -> t -> blk seq

  (** Returns the label of the entry block. *)
  val entry : t -> Label.t

  (** Returns the arguments of the function, along with their types. *)
  val args : ?rev:bool -> t -> (Var.t * Type.arg) seq

  (** Returns the return type of the function, if it exists. *)
  val return : t -> Type.arg option

  (** Returns [true] if the function is variadic. *)
  val variadic : t -> bool

  (** Returns [true] if the function does not return. *)
  val noreturn : t -> bool

  (** Returns the linkage of the function.

      If no value was given for it in the [dict], then the result defaults
      to [Linkage.default_export].
  *)
  val linkage : t -> Linkage.t

  (** Returns the dictionary of the function. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the function. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag fn t v] binds [v] to tag [t] in the dictionary of [fn]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the function has the associated name. *)
  val has_name : t -> string -> bool

  (** Returns the function prototype. *)
  val typeof : t -> Type.proto

  (** Returns a mapping from block labels to blocks.

      @raise Invalid_argument if there are duplicate labels
  *)
  val map_of_blks : t -> blk Label.Tree.t

  (** [map_blks fn ~f] returns [fn] with each basic block applied to [f].

      Note that [f] is allowed to change the label of the entry block.
      This change is reflected in the updated function.
  *)
  val map_blks : t -> f:(blk -> blk) -> t

  (** Same as [map_blks], but handles the case where [f] may fail. *)
  val map_blks_err : t -> f:(blk -> blk Or_error.t) -> t Or_error.t

  (** Appends a block to the end of the function. *)
  val insert_blk : t -> blk -> t

  (** Appends a slot to the function. *)
  val insert_slot : t -> slot -> t

  (** Removes a slot from the function. *)
  val remove_slot : t -> Var.t -> t

  (** [remove_blk_exn fn l] removes the block with label [l] from function
      [f].

      @raise Invalid_argument if [l] is the label of the entry block.
  *)
  val remove_blk_exn : t -> Label.t -> t

  (** Same as [remove_blk_exn], but returns an error upon failure. *)
  val remove_blk : t -> Label.t -> t Or_error.t

  (** Same as [remove_blk_exn], but removes multiple blocks.

      @raise Invalid_argument if one of the labels is the entry block.
  *)
  val remove_blks_exn : t -> Label.t list -> t

  (** Same as [remove_blks_exn], but returns an error if one of the labels
      is the entry block. *)
  val remove_blks : t -> Label.t list -> t Or_error.t

  (** [prepend_arg ?before fn x t] adds the argument [x] of type [t] to [fn].

      If [before] is [None], then [x] is inserted at the beginning of the
      argument list.

      If [before] is [Some y], then [x] will appear directly before the
      argument [y]. If [y] doesn't exist, then [x] is not inserted.
  *)
  val prepend_arg : ?before:Var.t option -> t -> Var.t -> Type.arg -> t

  (** [append_arg ?after fn x t] adds the argument [x] of type [t] to [fn].

      If [after] is [None], then [x] is inserted at the end of the
      argument list.

      If [after] is [Some y], then [x] will appear directly after the
      argument [y]. If [y] doesn't exist, then [x] is not inserted.
  *)
  val append_arg : ?after:Var.t option -> t -> Var.t -> Type.arg -> t

  (** [remove_arg fn x] removes the argument [x] from [fn], if it exists. *)
  val remove_arg : t -> Var.t -> t

  (** Returns [true] if the function has a block associated with the given
      label. *)
  val has_blk : t -> Label.t -> bool

  (** Finds the block with the associated label, if it exists. *)
  val find_blk : t -> Label.t -> blk option

  (** Returns the next block (after the given label) if it exists. *)
  val next_blk : t -> Label.t -> blk option

  (** Returns the previous block (before the given label) if it exists. *)
  val prev_blk : t -> Label.t -> blk option

  (** [update_blk_exn fn b] returns [fn] with block [b] updated, if it exists. *)
  val update_blk : t -> blk -> t

  (** Same as [update_blk], but for a list of blocks for updating in batches,
      which should be more efficient.

      @raise Invalid_argument if the list of blocks contains duplicate labels.
  *)
  val update_blks_exn : t -> blk list -> t

  (** Same as [update_blks_exn], but returns an error if there is a duplicate
      block label. *)
  val update_blks : t -> blk list -> t Or_error.t

  include Regular.S with type t := t
end

type func = Func.t [@@deriving bin_io, compare, equal, sexp]

(** The control-flow graph of the function. *)
module Cfg : sig
  include Graph
    with type node = Label.t
     and type Node.label = Label.t
     and type Edge.label = edge

  (** Creates the control-flow graph.

      Each node of the graph is the label of a basic block in the function,
      and edges between basic blocks are labeled according to the type of
      control-flow instruction that links them (see the [Edge] module).

      Additionally, two pseudo-labels are added to the graph ([Label.pseudoentry]
      and [Label.pseudoexit]). These labels link with each "entry" and "exit"
      node in the function, respectively. This representation is useful for
      computing the dominator tree of the function in question.
  *)
  val create : func -> t
end

type cfg = Cfg.t

(** Helpers for computing liveness of a function. *)
module Live : sig
  type t

  (** [compute fn ~keep] solves the data flow equations for liveness in
      the function [fn].

      [keep] is a set of variables that are initially live on the exit
      nodes of the function.
  *)
  val compute : ?keep:Var.Set.t -> func -> t

  (** The set of live-in variables at the block assicated with the label. *)
  val ins : t -> Label.t -> Var.Set.t

  (** The set of live-out variables at the block assicated with the label. *)
  val outs : t -> Label.t -> Var.Set.t

  (** The set of blocks where the variable is live-in. *)
  val blks : t -> Var.t -> Label.Set.t

  (** The set of variables that were defined in the block associated with
      the label. *)
  val defs : t -> Label.t -> Var.Set.t

  (** Returns the live-out mappings for each instruction in a given block.

      Note that this mapping does not cross block boundaries. It should be
      used to identify variables that are live within the scope of a single
      block.
  *)
  val insns : t -> Label.t -> Var.Set.t Label.Tree.t

  (** The set of variables that were used in the block associated with the
      label.

      Note that this set only includes the free variables of the block.
  *)
  val uses : t -> Label.t -> Var.Set.t

  (** Folds over the live-ins of each block.

      Applies [f] to the live-in set of each block in the function.
  *)
  val fold : t -> init:'a -> f:('a -> Label.t -> Var.Set.t -> 'a) -> 'a

  (** Returns the solution of the data-flow equations, which is a mapping
      from block labels to their live-out sets. *)
  val solution : t -> (Label.t, Var.Set.t) Solution.t

  (** Pretty-prints the live-in sets for each block. *)
  val pp : Format.formatter -> t -> unit
end

type live = Live.t

(** Abstract interpretation over intervals. *)
module Intervals : sig
  (** Mapping of variables to intervals. *)
  type state [@@deriving equal, sexp]

  (** The empty mapping. *)
  val empty_state : state

  (** Finds the interval associated with a variable, if it exists. *)
  val find_var : state -> Var.t -> Bv_interval.t option

  (** Enumerates the mapping. *)
  val enum_state : state -> (Var.t * Bv_interval.t) seq

  (** The analysis results. *)
  type t

  (** [insn t l] returns the output state of the instruction [l], if it
      exists. Otherwise, [empty_state] is returned. *)
  val insn : t -> Label.t -> state

  (** [input t l] returns the input state of the basic block [l], if it
      exists. Otherwise, [empty_state] is returned. *)
  val input : t -> Label.t -> state

  (** Performs the interval analysis.

      [word] is the pointer size for the target.

      [typeof] is the typing relation for variables.

      [steps] is an upper bound on the number of iterations before
      a fixed point can be reached.

      @raise Invalid_argument if the function is not in SSA form.
  *)
  val analyze :
    ?steps:int ->
    func ->
    word:Type.imm_base ->
    typeof:(Var.t -> Type.t) ->
    t
end

(** Loop analysis of a function. *)
module Loops : sig
  (** The identifier of a loop. *)
  type loop [@@deriving compare, equal]

  (** The loop nesting level. *)
  type level [@@deriving compare, equal]

  (** The loop data. *)
  type data

  (** The loop analysis. *)
  type t

  (** [header d] gets the header block of the loop. *)
  val header : data -> Label.t

  (** [parent d] gets the parent loop, if it exists. *)
  val parent : data -> loop option

  (** [level d] gets the nesting level of the loop. *)
  val level : data -> level

  (** [analyze fn] performs the loop analysis of [fn]. *)
  val analyze : func -> t

  (** [get t x] returns the data for loop [x]. *)
  val get : t -> loop -> data

  (** [blk t l] returns the innermost loop for the block
      at label [l], if it exists. *)
  val blk : t -> Label.t -> loop option

  (** [mem t l] returns [true] if the block at label [l] is
      part of a loop. *)
  val mem : t -> Label.t -> bool

  (** [is_header t l] returns [true] if the block at label [l]
      is the header of a loop. *)
  val is_header : t -> Label.t -> bool

  (** [is_child_of t m n] returns [true] if [m = n] or [m] is
      nested in [n]. *)
  val is_child_of : t -> loop -> loop -> bool

  (** [is_in_loop t l n] returns [true] if the block at label [l] is
      a member of the loop [n]. *)
  val is_in_loop : t -> Label.t -> loop -> bool

  (** [loops_of t l] returns the sequence of loops that the block at
      label [l] is within, starting from the innermost loop. *)
  val loops_of : t -> Label.t -> loop seq

  val pp_loop : Format.formatter -> loop -> unit
  val pp_level : Format.formatter -> level -> unit
  val pp_data : Format.formatter -> data -> unit
end

type loops = Loops.t

(** A struct of data. *)
module Data : sig
  (** An element of the struct. It can be a [const], or one of the following:

      [`string s] is an instance of a string [s], represented as an array
      of bytes.

      [`zero n] is a zero-initialized array of [n] bytes. Note that [n <= 0]
      is illegal.
  *)
  type elt = [
    | const
    | `string of string
    | `zero   of int
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Pretty-prints an element of the struct. *)
  val pp_elt : Format.formatter -> elt -> unit

  (** Attributes of the struct *)
  module Tag : sig
    (** The alignment of the struct. *)
    val align : int Dict.tag

    (** The linkage of the struct. *)
    val linkage : Linkage.t Dict.tag
  end

  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a struct.

      @raise Invalid_argument if [elts] is empty, or if [elts] contains an
      element of the form [`basic (_, [])], or if align is [Some n] where
      [n] is not a positive power of 2.
  *)
  val create_exn :
    ?dict:Dict.t ->
    name:string ->
    elts:elt list ->
    unit ->
    t

  (** Same as [create_exn], but returns an error upon failure. *)
  val create :
    ?dict:Dict.t ->
    name:string ->
    elts:elt list ->
    unit ->
    t Or_error.t

  (** Returns the name associated with the struct. *)
  val name : t -> string

  (** Returns the elements of the struct. *)
  val elts : ?rev:bool -> t -> elt seq

  (** Returns the linkage of the struct.

      If no value was given for it in the [dict], then the result defaults
      to [Linkage.default_export].
  *)
  val linkage : t -> Linkage.t

  (** Returns the desired alignment, if any. *)
  val align : t -> int option

  (** Returns the dictionary of the struct. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the struct. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag d t v] binds [v] to tag [t] in the dictionary of [d]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the struct has the associated name. *)
  val has_name : t -> string -> bool

  (** Returns the corresponding compound type of the struct. *)
  val typeof : t -> Target.t -> Type.compound

  (** Prepends an element to the beginning of the structure. *)
  val prepend_elt : t -> elt -> t

  (** Appends an element to the end of the structure. *)
  val append_elt : t -> elt -> t

  (** Returns the structure with each element transformed by [f] *)
  val map_elts : t -> f:(elt -> elt) -> t

  include Regular.S with type t := t
end

type data = Data.t [@@deriving bin_io, compare, equal, sexp]

(** A module is a single translation unit. *)
module Module : sig
  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a module. *)
  val create :
    ?dict:Dict.t ->
    ?typs:Type.compound list ->
    ?data:data list ->
    ?funs:func list ->
    name:string ->
    unit ->
    t

  (** The name of the module. *)
  val name : t -> string

  (** Declared (compound) types that are visible in the module. *)
  val typs : ?rev:bool -> t -> Type.compound seq

  (** Structs defined in the module. *)
  val data : ?rev:bool -> t -> data seq

  (** Functions defined in the module. *)
  val funs : ?rev:bool -> t -> func seq

  (** Returns the dictionary of the module. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the module. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag m t v] binds [v] to tag [t] in the dictionary of [m]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the module has the associated name. *)
  val has_name : t -> string -> bool

  (** Appends a type to the module. *)
  val insert_type : t -> Type.compound -> t

  (** Appends a struct to the module. *)
  val insert_data : t -> data -> t

  (** Appends a function to the module. *)
  val insert_fn : t -> func -> t

  (** Removes the type associated with the name. *)
  val remove_type : t -> string -> t

  (** Removes the struct associated with the name. *)
  val remove_data : t -> string -> t

  (** Removes the function associated with the name. *)
  val remove_fn : t -> string -> t

  (** Returns the module with each type transformed by [f]. *)
  val map_typs : t -> f:(Type.compound -> Type.compound) -> t

  (** Returns the module with each struct transformed by [f]. *)
  val map_data : t -> f:(data -> data) -> t

  (** Returns the module with each function transformed by [f]. *)
  val map_funs : t -> f:(func -> func) -> t

  (** Replaces the functions in the module. *)
  val with_funs : t -> func list -> t

  (** Returns the module with each type transformed by [f],
      where [f] may fail. *)
  val map_typs_err :
    t -> f:(Type.compound -> Type.compound Or_error.t) -> t Or_error.t

  (** Returns the module with each struct transformed by [f],
      where [f] may fail. *)
  val map_data_err : t -> f:(data -> data Or_error.t) -> t Or_error.t

  (** Returns the module with each function transformed by [f],
      where [f] may fail. *)
  val map_funs_err : t -> f:(func -> func Or_error.t) -> t Or_error.t

  include Regular.S with type t := t
end

type module_ = Module.t
