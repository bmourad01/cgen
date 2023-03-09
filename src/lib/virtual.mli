(** The virtual, target-agnostic machine, represented as a
    control-flow graph (CFG).

    It is used as the entry-level IR for the pipeline, to
    perform transformations that are not target-specific.
*)

open Core
open Graphlib.Std
open Regular.Std

(** A constant value.

    [`int n] is a constant integer value.

    [`float f] is a single-precision floating-point value.

    [`double d] is a double-precision floating-point value.

    [`sym (s, n)] is a reference to a global symbol [s], with a
    constant offset [n].
*)
type const = [
  | `int    of Bitvec.t
  | `float  of Float32.t
  | `double of float
  | `sym    of string * int
] [@@deriving bin_io, compare, equal, sexp]

(** Pretty-prints a constant value. *)
val pp_const : Format.formatter -> const -> unit

(** An instruction. *)
module Insn : sig
  (** An argument to an instruction. *)
  type arg = [
    | const
    | `var of Var.t
  ] [@@deriving bin_io, compare, equal, sexp]

  (** [var_of_arg a] returns [Some x] if [a] is a variable [x]. *)
  val var_of_arg : arg -> Var.t option

  (** Pretty-prints an argument to an instruction. *)
  val pp_arg : Format.formatter -> arg -> unit

  (** Inter-function destination.

      [`addr a] is a static absolute addrsss.

      [`sym s] is a global symbol.

      [`var v] is a dynamic absolute address.
  *)
  type global = [
    | `addr of Bitvec.t
    | `sym  of string
    | `var  of Var.t
  ] [@@deriving bin_io, compare, equal, sexp]

  (** [var_of_global g] returns [Some x] if [g] is a variable [x]. *)
  val var_of_global : global -> Var.t option

  (** Pretty-prints the global destination. *)
  val pp_global : Format.formatter -> global -> unit

  (** Intra-function destination.

      [`label (l, a)] is the label [l] of a block in the current function,
      with an optional argument [a].
  *)
  type local = [
    | `label of Label.t * arg list
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Pretty-prints the local destination. *)
  val pp_local : Format.formatter -> local -> unit

  (** The destination for a control flow instruction. *)
  type dst = [
    | global
    | local
  ] [@@deriving bin_io, compare, equal, sexp]

  (** [var_of_dst d] returns [Some x] if [d] is a variable [x]. *)
  val var_of_dst : dst -> Var.t option

  (** Pretty-prints a control-flow destination. *)
  val pp_dst : Format.formatter -> dst -> unit

  (** Data-flow-effectful instructions. *)
  module Data : sig
    (** Arithmetic binary operations.

        [`add t]: addition.

        [`div t]: division.

        [`mul t]: multiplication.

        [`rem t]: remainder.

        [`sub t]: subtraction.

        [`udiv t]: unsigned division (immediate only).

        [`urem t]: unsigned remainder (immediate only).
    *)
    type arith_binop = [
      | `add  of Type.basic
      | `div  of Type.basic
      | `mul  of Type.basic
      | `rem  of Type.basic
      | `sub  of Type.basic
      | `udiv of Type.imm
      | `urem of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints the arithmetic binary operator. *)
    val pp_arith_binop : Format.formatter -> arith_binop -> unit

    (** Arithmetic unary operations.

        [`neg t]: negation.
    *)
    type arith_unop = [
      | `neg of Type.basic
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints the arithmetic unary operator. *)
    val pp_arith_unop : Format.formatter -> arith_unop -> unit

    (** Bitwise binary operations.

        [`and_ t]: bitwise intersection (AND).

        [`or_ t]: bitwise union (OR).

        [`sar t]: arithmetic shift right.

        [`shl t]: logical shift left.

        [`shr t]: logical shift right.

        [`xor t]: bitwise difference (exclusive-OR).
    *)
    type bitwise_binop = [
      | `and_ of Type.imm
      | `or_  of Type.imm
      | `sar  of Type.imm
      | `shl  of Type.imm
      | `shr  of Type.imm
      | `xor  of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints the bitwise binary operator. *)
    val pp_bitwise_binop : Format.formatter -> bitwise_binop -> unit

    (** Bitwise unary operations.

        [`not_ t]: bitwise complement (NOT).
    *)
    type bitwise_unop = [
      | `not_ of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints the bitwise unary operator. *)
    val pp_bitwise_unop : Format.formatter -> bitwise_unop -> unit

    (** Memory operations.

        [`alloc n]: allocate [n] bytes and return a pointer.

        [`load (t, m, a)]: load a value of type [t] from memory
        [m] at address [a].

        [`store (t, m, a, v)]: store a value [v] of type [t] to
        memory [m] at address [a].
    *)
    type mem = [
      | `alloc of int
      | `load  of Type.basic * Var.t * arg
      | `store of Type.basic * Var.t * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Returns the set of free variables in the memory operation. *)
    val free_vars_of_mem : mem -> Var.Set.t

    (** Pretty-prints a memory operation. *)
    val pp_mem : Format.formatter -> mem -> unit

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
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints a comparison operation. *)
    val pp_cmp : Format.formatter -> cmp -> unit

    (** Cast operations.

        [`bits t]: reinterpret the underlying bits to type [t].

        [`ftosi (t, i)]: cast a float of type [t] to a signed
        integer of type [i].

        [`ftoui (t, i)]: cast a float of type [t] to an unsigned
        integer of type [i].

        [`ftrunc t]: truncate a float to a float of type [t].

        [`itrunc t]: truncate an integer to an integer of type [t].

        [`sext t]: sign-extend an integer to an integer of type [t].

        [`sitof (t, f)]: cast a signed integer of type [t] to a float
        of type [f].

        [`uitof (t, f)]: cast an unsigned integer of type [t] to a
        float of type [f].

        [`zext t]: sign-extend an integer to an integer of type [t].
    *)
    type cast = [
      | `bits   of Type.basic
      | `ftosi  of Type.fp * Type.imm
      | `ftoui  of Type.fp * Type.imm
      | `ftrunc of Type.fp
      | `itrunc of Type.imm
      | `sext   of Type.imm
      | `sitof  of Type.imm * Type.fp
      | `uitof  of Type.imm * Type.fp
      | `zext   of Type.imm
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints a cast operation. *)
    val pp_cast : Format.formatter -> cast -> unit 

    (** Copy operations.

        [`copy t]: move to a destination of type [t]. Arguments of compound
        type are interpreted as a pointer.
    *)
    type copy = [
      | `copy of Type.basic
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints a copy operation. *)
    val pp_copy : Format.formatter -> copy -> unit

    (** All binary operations. *)
    type binop = [
      | arith_binop
      | bitwise_binop
      | cmp
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints the binary operator. *)
    val pp_binop : Format.formatter -> binop -> unit

    (** All unary operations. *)
    type unop = [
      | arith_unop
      | bitwise_unop
      | cast
      | copy
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Pretty-prints the unary operator. *)
    val pp_unop : Format.formatter -> unop -> unit

    (** All operations.

        [`binop (x, b, l, r)]: compute [b(l, r)] and store the result in [x].

        [`unop (x, u, a)]: compute [u(a)] and store the result in [x].

        [`mem (x, m)]: compute [m] and store the result in [x].

        [`select (x, t, c, l, r)]: evaluate [c]; if non-zero then select [l]
        and assign to [x], otherwise select [r]. Both [l] and [r] must have
        type [t].
    *)
    type op = [
      | `binop  of Var.t * binop * arg * arg
      | `unop   of Var.t * unop  * arg
      | `mem    of Var.t * mem
      | `select of Var.t * Type.basic * Var.t * arg * arg
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Returns the set of free variables in the operation. *)
    val free_vars_of_op : op -> Var.Set.t

    (** Pretty-prints an operation. *)
    val pp_op : Format.formatter -> op -> unit

    (** A call instruction.

        [`acall (x, t, f, args, vargs)]: call to [f] with arguments [args],
        returning a value of type [t] and assigning it to variable [x]. If
        [vargs] is non-empty, then the function call is variadic, and these
        arguments are to be passed in that fashion.

        [`call (f, args, vargs)]: same as [`acall], but does not explicitly
        assign a result.

        Note that variadic calls require at least one non-variadic argument.
    *)
    type call = [
      | `acall of Var.t * Type.basic * global * arg list * arg list
      | `call  of global * arg list * arg list
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Returns the set of free variables in the call. *)
    val free_vars_of_call : call -> Var.Set.t

    (** Returns [true] if the call is variadic. *)
    val is_variadic : call -> bool

    (** Pretty-prints a call instruction. *)
    val pp_call : Format.formatter -> call -> unit

    (** A variadic argument instruction.

        [`vastart x] initializes [x] with a pointer to the start of the
        variadic argument list for the current function.
    *)
    type variadic = [
      | `vastart of Var.t
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Returns the set of free variables in the variadic argument
        instruction. *)
    val free_vars_of_variadic : variadic -> Var.Set.t

    (** Pretty-prints a variadic argument instruction. *)
    val pp_variadic : Format.formatter -> variadic -> unit

    (** A data instruction is either a call or a simple op. *)
    type t = [
      | call
      | op
      | variadic
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Returns the assigned variable of the operation, if it exists. *)
    val lhs : t -> Var.t option

    (** [has_lhs d x] returns [true] if the instruction [d] assigns the
        variable [x]. *)
    val has_lhs : t -> Var.t -> bool

    (** Returns the set of free variables in the data instruction. *)
    val free_vars : t -> Var.Set.t

    (** Pretty-prints a data instruction. *)
    val pp : Format.formatter -> t -> unit
  end

  (** Control-flow-effectful instructions. *)
  module Ctrl : sig
    (** A switch table. *)
    module Table : sig
      type t [@@deriving bin_io, compare, equal, sexp]

      (** Creates a switch table from an association list.Afl_instrument

          @raise Invalid_argument if the list has duplicate keys.
      *)
      val create_exn : (Bitvec.t * local) list -> t

      (** Same as [create_exn], but returns an error upon failure. *)
      val create : (Bitvec.t * local) list -> t Or_error.t

      (** Returns the elements of the table. *)
      val enum : t -> (Bitvec.t * local) seq

      (** [find t v] searches the table [t] for the label associated
          with the constant [v]. *)
      val find : t -> Bitvec.t -> local option

      (** [map_exn t ~f] applies [f] to each element of [t].

          @raise Invalid_argument if [f] produces a duplicate key.
      *)
      val map_exn : t -> f:(Bitvec.t -> local -> Bitvec.t * local) -> t

      (** Same as [map_exn], but returns [Error _] if [f] produces a
          duplicate key. *)
      val map : t -> f:(Bitvec.t -> local -> Bitvec.t * local) -> t Or_error.t
    end

    type table = Table.t [@@deriving bin_io, compare, equal, sexp]

    (** A control-flow instruction.

        [`hlt] terminates execution of the program. This is typically used
        to mark certain program locations as unreachable.

        [`jmp dst] is an unconditional jump to the destination [dst].

        [`jnz (cond, yes, no)] evaluates [cond] and jumps to [yes] if it
        is non-zero. Otherwise, the destination is [no].

        [`ret x] returns from a function. If the function returns a value,
        then [x] holds the value (and must not be [None]).

        [`switch (typ, index, default, table)] implements a jump table.
        For a variable [index] of type [typ], it will find the associated
        label of [index] in [table] and jump to it, if it exists. If not,
        then the destination of the jump is [default].
    *)
    type t = [
      | `hlt
      | `jmp    of dst
      | `jnz    of Var.t * dst * dst
      | `ret    of arg option
      | `switch of Type.imm * Var.t * local * table
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Returns the set of free variables in the control-flow instruction. *)
    val free_vars : t -> Var.Set.t

    (** Pretty-prints a control-flow instruction. *)
    val pp : Format.formatter -> t -> unit
  end

  (** An instruction with a label. *)
  type 'a t [@@deriving bin_io, compare, equal, sexp]

  type data = Data.t t [@@deriving bin_io, compare, equal, sexp]
  type ctrl = Ctrl.t t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a labeled data instruction. *)
  val data : Data.t -> label:Label.t -> data

  (** Creates a labeled control instruction. *)
  val ctrl : Ctrl.t -> label:Label.t -> ctrl

  (** Returns the underlying data of the instruction. *)
  val insn : 'a t -> 'a

  (** Returns the label of the instruction. *)
  val label : 'a t -> Label.t

  (** Returns [true] if the instruction has the given label. *)
  val has_label : 'a t -> Label.t -> bool

  (** Returns the hash of the instruction label. *)
  val hash : 'a t -> int

  (** Returns the assigned variable of the data instruction, if it exists. *)
  val lhs_of_data : data -> Var.t option

  (** Transforms the data instruction with [f]. *)
  val map_data : data -> f:(Data.t -> Data.t) -> data

  (** Transforms the control-flow instruction with [f]. *)
  val map_ctrl : ctrl -> f:(Ctrl.t -> Ctrl.t) -> ctrl

  (** Returns the set of free variables in the data instruction. *)
  val free_vars_of_data : data -> Var.Set.t

  (** Returns the set of free variables in the control-flow instruction. *)
  val free_vars_of_ctrl : ctrl -> Var.Set.t

  (** Pretty-prints a data instruction. *)
  val pp_data : Format.formatter -> data -> unit

  (** Pretty-prints a control instruction. *)
  val pp_ctrl : Format.formatter -> ctrl -> unit
end

(** A control-flow edge. *)
module Edge : sig
  (** The kinds of edges that may occur:

      [`always]: unconditional jump.

      [`true_ x]: taken if [x] is non-zero.

      [`false_ x]: taken if [x] is zero.

      [`switch_ (x, v)]: taken if [x = v].

      [`default x]: taken if [x] doesn't match any entry in the switch table.
  *)
  type t = [
    | `always
    | `true_ of Var.t
    | `false_ of Var.t
    | `switch of Var.t * Bitvec.t
    | `default of Var.t
  ] [@@deriving bin_io, compare, equal, sexp]

  include Regular.S with type t := t
end

type edge = Edge.t [@@deriving bin_io, compare, equal, sexp]

(** A basic block. *)
module Blk : sig
  (** The type of an argument to a block. *)
  type arg_typ = [
    | Type.basic
    | Type.special
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Pretty-prints the type of an argument. *)
  val pp_arg_typ : Format.formatter -> arg_typ -> unit

  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a basic block. *)
  val create :
    ?args:(Var.t * arg_typ) list ->
    ?data:Insn.data list ->
    label:Label.t ->
    ctrl:Insn.ctrl ->
    unit ->
    t

  (** Returns the label of the basic block. *)
  val label : t -> Label.t

  (** Returns the arguments of the basic block. *)
  val args : ?rev:bool -> t -> (Var.t * arg_typ) seq

  (** Returns the sequence of data instructions. *)
  val data : ?rev:bool -> t -> Insn.data seq

  (** Returns the control-flow instruction (also called the terminator)
      of the block. *)
  val ctrl : t -> Insn.ctrl

  (** [has_label b l] returns [true] if block [b] has label [l]. *)
  val has_label : t -> Label.t -> bool

  (** Returns the hash of the block label. *)
  val hash : t -> int

  (** Returns the set of free variables in the block.

      Note: this calculation does not traverse phi instructions.
  *)
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
  val has_data : t -> Label.t -> bool

  (** Returns [true] if the block has a control-flow instruction associated
      with the label. *)
  val has_ctrl : t -> Label.t -> bool

  (** Finds the data instruction with the associated label. *)
  val find_data : t -> Label.t -> Insn.data option

  (** Finds the control-flow instruction with the associated label. *)
  val find_ctrl : t -> Label.t -> Insn.ctrl option

  (** Returns the next data instruction (after the given label) if it
      exists. *)
  val next_data : t -> Label.t -> Insn.data option

  (** Returns the previous data instruction (before the given label) if it
      exists. *)
  val prev_data : t -> Label.t -> Insn.data option

  (** Applies [f] to each argument of the block. *)
  val map_args : t -> f:(Var.t -> arg_typ -> Var.t * arg_typ) -> t

  (** [map_data b ~f] returns [b] with each data instruction applied
      to [f]. *)
  val map_data : t -> f:(Label.t -> Insn.Data.t -> Insn.Data.t) -> t

  (** [map_ctrl b ~f] returns [b] with the terminator applied to [f]. *)
  val map_ctrl : t -> f:(Label.t -> Insn.Ctrl.t -> Insn.Ctrl.t) -> t

  (** [prepend_arg b a ?before] prepends the argument [a] to the block

      If [before] is [None], then [a] is inserted at the beginning of
      the argument list.

      If [before] is [Some x], then [a] will appear directly before the
      argument [x]. If [x] doesn't exist, then [a] is not inserted.
  *)
  val prepend_arg : ?before:Var.t option -> t -> (Var.t * arg_typ) -> t

  (** [append_arg b a ?after] appends the argument [a] to the block [b].

      If [after] is [None], then [a] is inserted at the end of the
      argument list.

      If [after] is [Some x], then [a] will appear directly after the
      argument [x]. If [x] doesn't exist, then [a] is not inserted.
  *)
  val append_arg : ?after:Var.t option -> t -> (Var.t * arg_typ) -> t

  (** [prepend_data b d ?before] prepends the data instruction [d] to
      the block [b].

      If [before] is [None], then [d] is inserted at the beginning of
      the data instructions.

      If [before] is [Some l], then [d] will appear directly before the
      data instruction at label [l]. If [l] doesn't exist, then [d] is
      not inserted.
  *)
  val prepend_data : ?before:Label.t option -> t -> Insn.data -> t

  (** [append_data b d ?after] appends the data instruction [d] to
      the block [b].

      If [after] is [None], then [d] is inserted at the end of the
      data instructions.

      If [after] is [Some l], then [d] will appear directly after the
      data instruction at label [l]. If [l] doesn't exist, then [d] is
      not inserted.
  *)
  val append_data : ?after:Label.t option -> t -> Insn.data -> t

  (** [remove_arg b x] removes an argument [x] from the block [b],
      if it exists. *)
  val remove_arg : t -> Var.t -> t

  (** [remove_data b l] removes a data instruction with label [l] from
      the block [b], if it exists. *)
  val remove_data : t -> Label.t -> t

  (** [has_arg b x] returns true if [b] has an argument [x]. *)
  val has_arg : t -> Var.t -> bool

  (** [typeof_arg b x] returns the type of argument [x] to [b], if it
      exists. *)
  val typeof_arg : t -> Var.t -> arg_typ option

  (** [has_lhs b x] returns [true] if a data instruction in [b] defines
      [x]. *)
  val has_lhs : t -> Var.t -> bool

  (** Same as [has_lhs], but also includes arguments to the block. *)
  val defines_var : t -> Var.t -> bool

  include Regular.S with type t := t
end

type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]

(** A function. *)
module Func : sig
  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a function.

      By default, [linkage] is [Linkage.default_export].

      It is assumed that [blks] is ordered such that the entry block is
      the first element.

      @raise Invalid_argument if [blks] is empty.
  *)
  val create_exn :
    ?return:Type.arg option ->
    ?variadic:bool ->
    ?noreturn:bool ->
    ?linkage:Linkage.t ->
    name:string ->
    blks:blk list ->
    args:(Var.t * Type.arg) list ->
    unit ->
    t

  (** Same as [create_exn], but returns an error upon failure. *)
  val create :
    ?return:Type.arg option ->
    ?variadic:bool ->
    ?noreturn:bool ->
    ?linkage:Linkage.t ->
    name:string ->
    blks:blk list ->
    args:(Var.t * Type.arg) list ->
    unit ->
    t Or_error.t

  (** Returns the name of the function. *)
  val name : t -> string

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

  (** Returns the linkage of the function. *)
  val linkage : t -> Linkage.t

  (** Returns [true] if the function has the associated name. *)
  val has_name : t -> string -> bool

  (** Returns the hash of the function name. *)
  val hash : t -> int

  (** Returns a mapping from block labels to blocks. *)
  val map_of_blks : t -> blk Label.Map.t

  (** [map_blks fn ~f] returns [fn] with each basic block applied to [f].

      Note that [f] is allowed to change the label of the entry block.
      This change is reflected in the updated function.
  *)
  val map_blks : t -> f:(blk -> blk) -> t

  (** Appends a block to the end of the function. *)
  val insert_blk : t -> blk -> t

  (** [remove_blk_exn fn l] removes the block with label [l] from function
      [f].

      @raise Invalid_argument if [l] is the label of the entry block.
  *)
  val remove_blk_exn : t -> Label.t -> t

  (** Same as [remove_blk_exn], but returns an error upon failure. *)
  val remove_blk : t -> Label.t -> t Or_error.t

  (** Returns [true] if the function has a block associated with the given
      label. *)
  val has_blk : t -> Label.t -> bool

  (** Finds the block with the associated label, if it exists. *)
  val find_blk : t -> Label.t -> blk option

  (** Returns the next block (after the given label) if it exists. *)
  val next_blk : t -> Label.t -> blk option

  (** Returns the previous block (before the given label) if it exists. *)
  val prev_blk : t -> Label.t -> blk option

  (** [update_blk fn b] returns [fn] with block [b] updated, if it exists. *)
  val update_blk : t -> blk -> t

  include Regular.S with type t := t
end

type func = Func.t [@@deriving bin_io, compare, equal, sexp]

(** The control-flow graph of the function. *)
module Cfg : sig
  include Graph with type node = Label.t
                 and type Node.label = Label.t
                 and type Edge.label = edge

  (** Creates the control-flow graph. *)
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

  (** The set of variables that were used in the block associated with the
      label. *)
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

(** A struct of data. *)
module Data : sig
  (** An element of the struct.

      [`basic (t, cs)] is a list of constants [cs] of type [t]. Note that it
      is illegal for [cs] to be empty. That is, all data must be initialized.

      [`string s] is an instance of a string [s], represented as an array
      of bytes.

      [`zero n] is a zero-initialized array of [n] bytes. Note that [n <= 0]
      is illegal.
  *)
  type elt = [
    | `basic  of Type.basic * const list
    | `string of string
    | `zero   of int
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Pretty-prints an element of the struct. *)
  val pp_elt : Format.formatter -> elt -> unit

  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a struct.

      By default, [linkage] is [Linkage.default_export].

      By default, [align] is [None], and so the data will be aligned by the
      size of its largest element.

      @raise Invalid_argument if [elts] is empty, or if [elts] contains an
        element of the form [`basic (_, [])], or if align is [Some n] where
        [n < 1].
  *)
  val create_exn :
    ?align:int option ->
    ?linkage:Linkage.t ->
    name:string ->
    elts:elt list ->
    unit ->
    t

  (** Same as [create_exn], but returns an error upon failure. *)
  val create :
    ?align:int option ->
    ?linkage:Linkage.t ->
    name:string ->
    elts:elt list ->
    unit ->
    t Or_error.t

  (** Returns the name associated with the struct. *)
  val name : t -> string

  (** Returns the elements of the struct. *)
  val elts : ?rev:bool -> t -> elt seq

  (** Returns the linkage of the struct. *)
  val linkage : t -> Linkage.t

  (** Returns the desired alignment, if any. *)
  val align : t -> int option

  (** Returns [true] if the struct has the associated name. *)
  val has_name : t -> string -> bool

  (** Returns the hash of the struct name. *)
  val hash : t -> int

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

  (** Returns [true] if the module has the associated name. *)
  val has_name : t -> string -> bool

  (** Returns the hash of the module's name. *)
  val hash : t -> int

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

  include Regular.S with type t := t
end

type module_ = Module.t
