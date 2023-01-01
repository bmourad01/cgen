(** The virtual, target-agnostic machine, represented as a
    control-flow graph (CFG).

    It is used as the entry-level IR for the pipeline, to
    perform transformations that are not target-specific.
*)

open Regular.Std

(** An instruction. *)
module Insn : sig
  (** A constant value. *)
  type const = [
    | `int   of Bitvec.t
    | `float of Decimal.t
    | `sym   of string
  ]

  (** An argument to an instruction. *)
  type arg = [
    | const
    | `var of Var.t
  ]

  (** [var_of_arg a] returns [Some x] if [a] is a variable [x]. *)
  val var_of_arg : arg -> Var.t option

  (** Pretty-prints an argument to an instruction. *)
  val pp_arg : Format.formatter -> arg -> unit

  (** Inter-function destination. *)
  type global = [
    | `addr of Bitvec.t
    | `sym  of string
    | `var  of Var.t
  ]

  (** Pretty-prints the global destination. *)
  val pp_global : Format.formatter -> global -> unit

  (** Intra-function destination. *)
  type local = [
    | `label of Label.t
  ]

  (** Pretty-prints the local destination. *)
  val pp_local : Format.formatter -> local -> unit

  (** The destination for a control flow instruction. *)
  type dst = [
    | global
    | local
  ]

  (** Pretty-prints a control-flow destination. *)
  val pp_dst : Format.formatter -> dst -> unit

  (** A phi instruction. *)
  module Phi : sig
    type t

    (** Creates a phi instruction.

        @raise Invalid_argument if [ins] has duplicate keys.
    *)
    val create :
      ?ins:(Label.t * arg) list ->
      lhs:Var.t ->
      typ:[Type.basic | Type.special] ->
      unit ->
      t

    (** The destination variable of the instruction. *)
    val lhs : t -> Var.t

    (** The type of the variable. *)
    val typ : t -> [Type.basic | Type.special]

    (** The incoming edges of the instruction. *)
    val ins : t -> (Label.t * arg) seq

    (** [has_lhs p x] [true] if the instruction [p] defines the
        variable [x]. *)
    val has_lhs : t -> Var.t -> bool

    (** Returns the set of free variables in the instruction. *)
    val free_vars : t -> Var.Set.t

    (** Pretty-prints a phi instruction. *)
    val pp : Format.formatter -> t -> unit
  end

  (** Data-flow-effectful instructions. *)
  module Data : sig
    (** Arithmetic operations. *)
    type arith = [
      | `add  of Type.basic * arg * arg
      | `div  of Type.basic * arg * arg
      | `mul  of Type.basic * arg * arg
      | `neg  of Type.basic * arg
      | `rem  of Type.basic * arg * arg
      | `sub  of Type.basic * arg * arg
      | `udiv of Type.basic * arg * arg
      | `urem of Type.basic * arg * arg
    ]

    (** Returns the set of free variables in the arithmetic operation. *)
    val free_vars_of_arith : arith -> Var.Set.t

    (** Pretty-prints an arithmetic operation. *)
    val pp_arith : Format.formatter -> arith -> unit

    (** Bitwise operations. *)
    type bits = [
      | `and_ of Type.imm * arg * arg
      | `or_  of Type.imm * arg * arg
      | `sar  of Type.imm * arg * arg
      | `shl  of Type.imm * arg * arg
      | `shr  of Type.imm * arg * arg
      | `xor  of Type.imm * arg * arg
    ]

    (** Returns the set of free variables in the bitwise operation. *)
    val free_vars_of_bits : bits -> Var.Set.t

    (** Pretty-prints a bitwise operation. *)
    val pp_bits : Format.formatter -> bits -> unit

    (** Memory operations. *)
    type mem = [
      | `alloc of int
      | `load  of Type.basic * Var.t * arg
      | `store of Type.basic * Var.t * arg * arg
    ]

    (** Returns the set of free variables in the memory operation. *)
    val free_vars_of_mem : mem -> Var.Set.t

    (** Pretty-prints a memory operation. *)
    val pp_mem : Format.formatter -> mem -> unit

    (** Comparison operations. *)
    type cmp = [
      | `eq  of Type.basic * arg * arg
      | `ge  of Type.basic * arg * arg
      | `gt  of Type.basic * arg * arg
      | `le  of Type.basic * arg * arg
      | `lt  of Type.basic * arg * arg
      | `ne  of Type.basic * arg * arg
      | `o   of Type.basic * arg * arg
      | `sge of Type.basic * arg * arg
      | `sgt of Type.basic * arg * arg
      | `sle of Type.basic * arg * arg
      | `slt of Type.basic * arg * arg
      | `uo  of Type.basic * arg * arg
    ]

    (** Returns the set of free variables in the comparison operation. *)
    val free_vars_of_cmp : cmp -> Var.Set.t

    (** Pretty-prints a comparison operation. *)
    val pp_cmp : Format.formatter -> cmp -> unit

    (** Cast operations. *)
    type cast = [
      | `bits   of Type.basic * arg
      | `ftosi  of Type.fp * Type.imm * arg
      | `ftoui  of Type.fp * Type.imm * arg
      | `ftrunc of Type.fp * arg
      | `itrunc of Type.imm * arg
      | `sext   of Type.imm * arg
      | `sitof  of Type.imm * Type.fp * arg
      | `uitof  of Type.imm * Type.fp * arg
      | `zext   of Type.imm * arg
    ]

    (** Returns the set of free variables in the cast operation. *)
    val free_vars_of_cast : cast -> Var.Set.t

    (** Pretty-prints a cast operation. *)
    val pp_cast : Format.formatter -> cast -> unit 

    (** Copy operations. *)
    type copy = [
      | `copy of Type.basic * arg
      | `select of Type.basic * Var.t * arg * arg
    ]

    (** Returns the set of free variables in the copy operation. *)
    val free_vars_of_copy : copy -> Var.Set.t

    (** Pretty-prints a copy operation. *)
    val pp_copy : Format.formatter -> copy -> unit

    (** All simple operations. *)
    type op = [
      | arith
      | bits
      | mem
      | cmp
      | cast
      | copy
    ]

    (** Returns the set of free variables in the operation. *)
    val free_vars_of_op : op -> Var.Set.t

    (** Pretty-prints an operation. *)
    val pp_op : Format.formatter -> op -> unit

    (** A call that does not assign a result.

        The [`callv] constructor is used to indicate a variadic
        call, hence the [v] suffix.
    *)
    type void_call = [
      | `call  of global * arg list
      | `callv of global * arg list
    ]

    (** Returns the set of free variables in the void call. *)
    val free_vars_of_void_call : void_call -> Var.Set.t

    (** A call that assigns a result, hence the [a] prefix in the
        constructor names.

        The [`acallv] constructor is used to indicate a variadic
        call, hence the [v] suffix.
    *)
    type assign_call = [
      | `acall  of Var.t * Type.basic * global * arg list
      | `acallv of Var.t * Type.basic * global * arg list
    ]

    (** Returns the set of free variables in the assign call. *)
    val free_vars_of_assign_call : assign_call -> Var.Set.t

    (** A call instruction. *)
    type call = [
      | void_call
      | assign_call
    ]

    (** Returns the set of free variables in the call. *)
    val free_vars_of_call : call -> Var.Set.t

    (** Returns [true] if the call is variadic. *)
    val is_variadic : call -> bool

    (** Pretty-prints a call instruction. *)
    val pp_call : Format.formatter -> call -> unit

    (** A data instruction is either a call or a simple op. *)
    type t = [
      | call
      | `op of Var.t * op
    ]

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
    type table

    (** Creates a switch table from an association list.Afl_instrument

        @raise [Invalid_argument] if the list has duplicate keys.
    *)
    val table : (Bitvec.t * Label.t) list -> table

    (** A control-flow instruction.

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
      | `jmp    of dst
      | `jnz    of Var.t * dst * dst
      | `ret    of arg option
      | `switch of Type.imm * Var.t * Label.t * table
    ]

    (** Returns the set of free variables in the control-flow instruction. *)
    val free_vars : t -> Var.Set.t

    (** Pretty-prints a control-flow instruction. *)
    val pp : Format.formatter -> t -> unit
  end

  (** An instruction with a label. *)
  type 'a t

  type phi = Phi.t t
  type data = Data.t t
  type ctrl = Ctrl.t t

  (** Creates a labeled phi instruction. *)
  val phi : Phi.t -> label:Label.t -> phi

  (** Creates a labeled data instruction. *)
  val data : Data.t -> label:Label.t -> data

  (** Creates a labeled control instruction. *)
  val ctrl : Ctrl.t -> label:Label.t -> ctrl

  (** Returns the underlying data of the instruction. *)
  val insn : 'a t -> 'a

  (** Returns the label of the instruction. *)
  val label : 'a t -> Label.t

  (** Returns the assigned variable of the phi instruction. *)
  val lhs_of_phi : phi -> Var.t

  (** Returns the assigned variable of the data instruction, if it exists. *)
  val lhs_of_data : data -> Var.t option

  (** Returns the set of free variables in the phi instruction. *)
  val free_vars_of_phi : phi -> Var.Set.t

  (** Returns the set of free variables in the data instruction. *)
  val free_vars_of_data : data -> Var.Set.t

  (** Returns the set of free variables in the control-flow instruction. *)
  val free_vars_of_ctrl : ctrl -> Var.Set.t

  (** Pretty-prints a phi instruction. *)
  val pp_phi : Format.formatter -> phi -> unit

  (** Pretty-prints a data instruction. *)
  val pp_data : Format.formatter -> data -> unit

  (** Pretty-prints a control instruction. *)
  val pp_ctrl : Format.formatter -> ctrl -> unit

  (** Pretty-prints a phi instruction with human-readable labels. *)
  val pp_phi_hum : Format.formatter -> phi -> unit

  (** Equivalent to [Data.pp]. *)
  val pp_data_hum : Format.formatter -> data -> unit

  (** Pretty-prints a control instruction with human-readable labels. *)
  val pp_ctrl_hum : Format.formatter -> ctrl -> unit
end

(** A basic block. *)
module Blk : sig
  type t

  (** Creates a basic block. *)
  val create :
    ?phi:Insn.phi list ->
    ?data:Insn.data list ->
    label:Label.t ->
    ctrl:Insn.ctrl ->
    unit ->
    t

  (** Returns the label of the basic block. *)
  val label : t -> Label.t

  (** Returns the phi functions of the basic block. *)
  val phi : t -> Insn.phi seq

  (** Returns the sequence of data instructions. *)
  val data : t -> Insn.data seq

  (** Returns the control-flow instruction (also called the terminator)
      of the block. *)
  val ctrl : t -> Insn.ctrl

  (** Returns the set of free variables in the block. *)
  val free_vars : t -> Var.Set.t

  (** [uses_var b x] returns [true] if the variable [x] appears in the
      free variables of [b]. *)
  val uses_var : t -> Var.t -> bool

  (** [defines_var b x] returns [true] if the variable [x] is defined
      in the block [b]. *)
  val defines_var : t -> Var.t -> bool

  (** [map_phi b ~f] returns [b] with each phi instruction applied
      to [f]. *)
  val map_phi : t -> f:(Insn.phi -> Insn.phi) -> t

  (** [map_data b ~f] returns [b] with each data instruction applied
      to [f]. *)
  val map_data : t -> f:(Insn.data -> Insn.data) -> t

  (** [concat_map_phi b ~f] is similar to [map_phi], but [f] instead
      returns a list of phi instructions, thus it could either add or
      remove phi instructions from [b]. *)
  val concat_map_phi : t -> f:(Insn.phi -> Insn.phi list) -> t

  (** [concat_map_data b ~f] is similar to [map_data], but [f] instead
      returns a list of data instructions, thus it could either add or
      remove data instructions from [b]. *)
  val concat_map_data : t -> f:(Insn.data -> Insn.data list) -> t

  (** [map_ctrl b ~f] returns [b] with the terminator applied to [f]. *)
  val map_ctrl : t -> f:(Insn.ctrl -> Insn.ctrl) -> t

  (** Inserts a phi instruction into the block. *)
  val insert_phi : t -> Insn.phi -> t

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

  (** Pretty prints a basic block. *)
  val pp : Format.formatter -> t -> unit

  (** Pretty prints a basic block, where instructions are indented and
      unlabeled. *)
  val pp_hum : Format.formatter -> t -> unit
end

type blk = Blk.t

(** A function. *)
module Fn : sig
  type t

  (** Creates a function.

      By default, [linkage] is [Linkage.default_export].

      @raise Invalid_argument if [blks] is empty.
  *)
  val create :
    ?return:Type.t option ->
    ?variadic:bool ->
    ?linkage:Linkage.t ->
    name:string ->
    blks:blk list ->
    args:(Var.t * Type.t) list ->
    unit ->
    t

  (** Returns the name of the function. *)
  val name : t -> string

  (** Returns the basic blocks of the function. *)
  val blks : t -> blk seq

  (** Returns the label of the entry point. *)
  val entry : t -> Label.t

  (** Returns the arguments of the function, along with their types. *)
  val args : t -> (Var.t * Type.t) seq

  (** Returns the return type of the function, if it exists. *)
  val return : t -> Type.t option

  (** Returns [true] if the function is variadic. *)
  val variadic : t -> bool

  (** Returns the linkage of the function. *)
  val linkage : t -> Linkage.t

  (** [map_blks fn ~f] returns [fn] with each basic block applied to [f]. *)
  val map_blks : t -> f:(blk -> blk) -> t

  (** Pretty-prints a function. *)
  val pp : Format.formatter -> t -> unit

  (** Pretty-prints a function where only blocks are labeled. *)
  val pp_hum : Format.formatter -> t -> unit
end

type fn = Fn.t
