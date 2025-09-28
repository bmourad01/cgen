(** The virtual, target-agnostic machine, represented as a
    control-flow graph (CFG).

    It is used as the entry-level IR for the pipeline, to
    perform transformations that are not target-specific.
*)

open Core
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
  include Virtual_insn_intf.S with type operand := operand

  include Virtual_insn_intf.Mem
    with type operand := operand
     and type ty := Type.arg

  (** A call instruction.

      [`call (a, f, args, vargs)]: call to [f] with arguments [args] and
      [vargs], where [vargs] is the list of variadic arguments. If [a]
      is [Some (x, t)], then the function returns a value of type [t],
      which is assigned to variable [x].

      Note that variadic calls require at least one non-variadic argument.
  *)
  type call = [
    | `call of (Var.t * Type.ret) option * global * operand list * operand list
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the call. *)
  val free_vars_of_call : call -> Var.Set.t

  (** Pretty-prints a call instruction. *)
  val pp_call : Format.formatter -> call -> unit

  (** Returns [true] if the call is variadic. *)
  val is_variadic : call -> bool

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

  (** Returns the set of free variables in the data operation. *)
  val free_vars_of_op : op -> Var.Set.t

  (** Pretty-prints a data operation. *)
  val pp_op : Format.formatter -> op -> unit

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

  (** Returns the assigned variable of the operation, if it exists. *)
  val lhs_of_op : op -> Var.t option

  (** [has_lhs d x] returns [true] if the instruction [d] assigns the
      variable [x]. *)
  val op_has_lhs : op -> Var.t -> bool
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
module Ctrl : Virtual_ctrl_intf.S
  with type operand := operand
   and type local := local
   and type dst := dst
   and type ret := operand option

type ctrl = Ctrl.t [@@deriving bin_io, compare, equal, sexp]

(** A basic block. *)
module Blk : sig
  include Virtual_blk_intf.S
    with type op := Insn.op
     and type insn := insn
     and type ctrl := ctrl
end

type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]

(** A stack slot. *)
module Slot : sig
  type t [@@deriving bin_io, compare, equal, hash, sexp]

  (** [create_exn x ~size ~align] creates a slot for variable [x] with
      [size] and [align].

      The [size] and [align]ment are the minimum such values for any
      given slot, and they may be increased according to the needs of
      the target ABI.

      @raise Invalid_argument if [size < 0], [align < 1], or [align] is
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

  include Regular.S with type t := t
end

type slot = Slot.t [@@deriving bin_io, compare, equal, sexp]

(** A function. *)
module Func : sig
  include Virtual_func_intf.S
    with type blk := blk
     and type arg := Var.t
     and type argt := Type.arg
     and type slot := slot

  (** Tags for various information about the function. *)
  module Tag : sig
    (** The return type of the function, paired with a flag
        indicating whether the result should be interpreted
        as signed. *)
    val return : Type.ret Dict.tag

    (** Indicates whether the function is variadic or not. *)
    val variadic : unit Dict.tag

    (** Indicates whether the function should be interpreted
        as not returning. *)
    val noreturn : unit Dict.tag

    (** The linkage of the function. *)
    val linkage : Linkage.t Dict.tag
  end

  (** Returns the return type of the function, if it exists. *)
  val return : t -> Type.ret option

  (** Returns [true] if the function is variadic. *)
  val variadic : t -> bool

  (** Returns [true] if the function does not return. *)
  val noreturn : t -> bool

  (** Returns the linkage of the function.

      If no value was given for it in the [dict], then the result defaults
      to [Linkage.default_export].
  *)
  val linkage : t -> Linkage.t

  (** Returns the function prototype. *)
  val typeof : t -> Type.proto
end

type func = Func.t [@@deriving bin_io, compare, equal, sexp]

(** The control-flow graph of the function. *)
module Cfg : sig
  include Label.Graph_s

  (** Creates the control-flow graph.

      Each node of the graph is the label of a basic block in the function,
      and edges between basic blocks correspond to control-flow transfers
      between them.

      Additionally, two pseudo-labels are added to the graph ([Label.pseudoentry]
      and [Label.pseudoexit]). These labels link with each "entry" and "exit"
      node in the function, respectively. This representation is useful for
      computing the dominator tree of the function in question.
  *)
  val create : func -> t
end

type cfg = Cfg.t

(** Helpers for computing liveness of a function. *)
module Live : Live_intf.S
  with type var := Var.t
   and type var_comparator := Var.comparator_witness
   and type func := func
   and type blk := blk
   and type cfg := cfg

type live = Live.t

(** Helpers for resolving labels to instructions/blocks. *)
module Resolver : Resolver_intf.S
  with type lhs := Var.t option
   and type insn := insn
   and type blk := blk
   and type func := func

type resolver = Resolver.t

module Loops : Loops_intf.S with type func := func

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

    (** Indicates that the struct is read-only. *)
    val const : unit Dict.tag
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

  (** Returns [true] if the struct is read-only. *)
  val const : t -> bool

  (** Returns the dictionary of the struct. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the struct. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag d t v] binds [v] to tag [t] in the dictionary of [d]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the struct has the associated name. *)
  val has_name : t -> string -> bool

  (** Returns the corresponding compound type of the struct, where
      [word] is the target's pointer size. *)
  val typeof : t -> word:Type.imm_base -> Type.compound

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
  include Virtual_module_intf.S
    with type data := data
     and type func := func

  (** Creates a module. *)
  val create :
    ?dict:Dict.t ->
    ?typs:Type.compound list ->
    ?data:data list ->
    ?funs:func list ->
    name:string ->
    unit ->
    t

  (** Declared (compound) types that are visible in the module. *)
  val typs : ?rev:bool -> t -> Type.compound seq

  (** Appends a type to the module. *)
  val insert_type : t -> Type.compound -> t

  (** Removes the type associated with the name. *)
  val remove_type : t -> string -> t

  (** Returns the module with each type transformed by [f]. *)
  val map_typs : t -> f:(Type.compound -> Type.compound) -> t

  (** Returns the module with each type transformed by [f],
      where [f] may fail. *)
  val map_typs_err :
    t -> f:(Type.compound -> Type.compound Or_error.t) -> t Or_error.t
end

type module_ = Module.t

(** The Virtual IR, lowered to conform to a specific ABI. *)
module Abi : sig
  module Insn : sig
    include Virtual_insn_intf.S with type operand := operand

    include Virtual_insn_intf.Mem
      with type operand := operand
       and type ty := Type.basic

    (** An argument to a call instruction.

        [`reg (a, r)]: the argument is passed in a register [r].

        [`stk (a, o)]: the argument [a] is passed at stack offset [o].
    *)
    type callarg = [
      | `reg of operand * string
      | `stk of operand * int
    ] [@@deriving bin_io, compare, equal, sexp]

    val free_vars_of_callarg : callarg -> Var.Set.t

    val pp_callarg : Format.formatter -> callarg -> unit

    (** A call instruction.

        [`call (xs, f, args)] calls the function [f] with [args], returning
        zero or more results in [xs]. Each [x \in xs] is a tuple [(x, t, r)],
        where [x] has type [t] and is bound to the register [r] that is returned
        from the call.
    *)
    type call = [
      | `call of (Var.t * Type.basic * string) list * global * callarg list
    ] [@@deriving bin_io, compare, equal, sexp]

    val free_vars_of_call : call -> Var.Set.t

    val pp_call : Format.formatter -> call -> unit

    (** Miscellaneous, ABI-specific instructions. Use with caution.

        [`regcopy (x, t, r)]: copy the register [r] into the variable [x],
        with type [t].

        [`regstore (r, a)]: store the register [v] at address [a].

        [`regassign (r, a)]: assign the value [a] to the register [r].

        [`stkargs x]: returns a pointer to the beginning of the memory region
        containing the arguments passed on the stack, and stores the result in
        [x]. This is particularly useful for implementing variadic arguments.
    *)
    type extra = [
      | `regcopy of Var.t * Type.basic * string
      | `regstore of string * operand
      | `regassign of string * operand
      | `stkargs of Var.t
    ] [@@deriving bin_io, compare, equal, sexp]

    val free_vars_of_extra : extra -> Var.Set.t

    val pp_extra : Format.formatter -> extra -> unit

    (** A data operation. *)
    type op = [
      | basic
      | call
      | mem
      | extra
    ] [@@deriving bin_io, compare, equal, sexp]

    (** Returns the set of free variables in the data operation. *)
    val free_vars_of_op : op -> Var.Set.t

    (** Pretty-prints a data operation. *)
    val pp_op : Format.formatter -> op -> unit

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

    (** Returns the set of defined variables of the instruction. *)
    val def : t -> Var.Set.t

    (** Same as [pp_op]. *)
    val pp : Format.formatter -> t -> unit

    (** Tags for various information about the instruction. *)
    module Tag : sig
      (** Do not attempt to transform this call into a tail call. *)
      val non_tail : unit Dict.tag
    end
  end

  type insn = Insn.t [@@deriving bin_io, compare, equal, sexp]

  module Ctrl : Virtual_ctrl_intf.S
    with type operand := operand
     and type local := local
     and type dst := dst
     and type ret := (string * operand) list

  type ctrl = Ctrl.t [@@deriving bin_io, compare, equal, sexp]

  module Blk : sig
    include Virtual_blk_intf.S
      with type op := Insn.op
       and type insn := insn
       and type ctrl := ctrl
  end

  type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]

  (** An ABI-lowered function.

      Note that an argument [a] in the [args] of a function may include
      a [`reg r], indicating that [a] is passed in register [r]. All
      other arguments are assumed to be passed in memory according to
      the target ABI.

      As a special case, [{prepend,append,remove}_arg] will use [same_arg]
      to test for equality.
  *)
  module Func : sig
    (** Tags for various information about the function. *)
    module Tag : sig
      (** Indicates whether the function is variadic or not. *)
      val variadic : unit Dict.tag

      (** The linkage of the function. *)
      val linkage : Linkage.t Dict.tag
    end

    (** An argument to the function.

        [`reg (x, r)]: the argument [x] is passed in register [r].

        [`stk (x, o)]: the argument [x] is passed at stack offset [o].
    *)
    type arg = [
      | `reg of Var.t * string
      | `stk of Var.t * int
    ] [@@deriving bin_io, compare, equal, sexp]

    (** [same_arg x y] returns [true] if [x] and [y] refer to the same
        register or variable; e.g. stack offsets are ignored. *)
    val same_arg : arg -> arg -> bool

    val pp_arg : Format.formatter -> arg -> unit

    include Virtual_func_intf.S
      with type blk := blk
       and type arg := arg
       and type argt := Type.basic
       and type slot := slot

    (** Returns [true] if the function takes a variable number of
        arguments (using [Func.Tag.variadic]). *)
    val variadic : t -> bool

    (** Returns the linkage of the function (using [Func.Tag.linkage]).

        If no value was given for it in the [dict], then the result defaults
        to [Linkage.default_export].
    *)
    val linkage : t -> Linkage.t
  end

  type func = Func.t [@@deriving bin_io, compare, equal, sexp]

  (** A translation unit. *)
  module Module : sig
    include Virtual_module_intf.S
      with type data := data
       and type func := func

    (** Creates a module. *)
    val create :
      ?dict:Dict.t ->
      ?data:data list ->
      ?funs:func list ->
      name:string ->
      unit ->
      t
  end

  type module_ = Module.t [@@deriving bin_io, compare, equal, sexp]

  module Cfg : sig
    include Label.Graph_s
    val create : func -> t
  end

  type cfg = Cfg.t

  module Live : Live_intf.S
    with type var := Var.t
     and type var_comparator := Var.comparator_witness
     and type func := func
     and type blk := blk
     and type cfg := cfg

  type live = Live.t

  module Resolver : Resolver_intf.S
    with type lhs := Var.Set.t
     and type insn := insn
     and type blk := blk
     and type func := func

  type resolver = Resolver.t
end
