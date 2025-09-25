(** The main interface for target machine implementations. *)

open Core

module type S_reg = sig
  (** A machine register. *)
  module Reg : sig
    type t [@@deriving bin_io, compare, equal, hash, sexp]

    (** Stack pointer register. *)
    val sp : t

    (** Frame pointer register. *)
    val fp : t

    (** A list of all general purpose registers, in order of their preference
        for register allocation, {b except for} [sp] and [fp], which
        {b must not} be contained. *)
    val allocatable : t list

    (** A list of all floating point registers, in order of their preference
        for register allocation. *)
    val allocatable_fp : t list

    (** Returns the class of the register. *)
    val classof : t -> Machine_regvar.cls

    (** The type of the register. *)
    val typeof : t -> [Type.basic | `v128]

    (** Returns [true] if the register must be preserved by the callee. *)
    val is_callee_save : t -> bool

    (** Returns [true] if the register is passed as an argument as part of
        the calling convention. *)
    val is_arg : t -> bool

    (** Pretty-print the register name. *)
    val pp : Format.formatter -> t -> unit

    (** Decode the register from a string.

        @raise Invalid_argument if the string is not a valid register name.
    *)
    val of_string_exn : string -> t

    (** Same as [of_string_exn], but returns [None] if the string is not a
        valid register name. *)
    val of_string : string -> t option
  end

  module Regvar : Machine_regvar.S with type reg := Reg.t
end

module type S_insn = sig
  include S_reg

  (** A machine instruction. *)
  module Insn : sig
    (** The abstract representation of an instruction. *)
    type t [@@deriving bin_io, compare, equal, sexp]

    (** The set of arguments that the instruction reads from. *)
    val reads : t -> Regvar.Set.t

    (** The set of arguments that the instruction writes to. *)
    val writes : t -> Regvar.Set.t

    (** The set of static destination labels.

        This is intended for instructions that affect control flow,
        which makes this function useful for computing the CFG.
    *)
    val dests : t -> Label.Set.t

    (** Returns [true] if the instruction writes data to memory. *)
    val writes_to_memory : t -> bool

    (** Returns [true] if the instruction should always be computed,
        if it is reachable. *)
    val always_live : t -> bool

    (** Returns [true] if the instruction does not implicitly fall through. *)
    val is_barrier : t -> bool

    (** Pretty-prints the instruction. *)
    val pp : Format.formatter -> t -> unit
  end
end

module type S = sig
  (** The target descriptor. *)
  val target : Target.t

  (** Align the given stack space for arguments passed to a function. *)
  val call_args_stack_size : int -> int

  (** The offset from the frame pointer that points to the starting location
      of arguments passed on the stack.

      This assumes that the stack frame has already been allocated.
  *)
  val stack_args_offset : int

  (** Does the machine natively support [uitof]? *)
  val supports_uitof : bool

  include S_insn

  (** Lowers the ABI-specific details of a function for a given target.

      The function is expected to be in SSA form.

      The resulting output is expected to preserve the function's [dict],
      specifically information about linkage and whether the function is
      variadic or not.
  *)
  module Lower_abi(C : Context_intf.S_virtual) : sig
    val run : Typecheck.env -> Virtual.func -> Virtual.Abi.func C.t
  end

  (** Instruction selection. *)
  module Isel(C : Context_intf.S) : sig
    (** Rewrite rules for instruction selection. *)
    val rules : (Regvar.t, Insn.t) Isel_rewrite.Rule(C).t list
  end

  (** Register allocation helpers. *)
  module Regalloc : sig
    (** If the instruction is a simple copy or move from one register/var to
        another, then return [Some (d, s)], where [d] is the destination
        and [s] is the source.

        Note that both [d] and [s] {b must} have the same register class.
    *)
    val is_copy : Insn.t -> (Regvar.t * Regvar.t) option

    (** Returns [true] if this is a call instruction, or an instruction that
        may otherwise clobber an arbitrary set of registers. *)
    val is_call : Insn.t -> bool

    (** Produce an instruction to load a value from a slot, where [src] holds the
        address of the slot and [dst] is destination register/variable. *)
    val load_from_slot : [Type.basic | `v128] -> dst:Regvar.t -> src:Regvar.t -> Insn.t

    (** Constructs a move instruction, copying from register [src] to [dst]. *)
    val move : [Type.basic | `v128] -> dst:Regvar.t -> src:Regvar.t -> Insn.t

    (** Produce an instruction to store a value to a slot, where [src] holds the
        value being stored and [dst] is the address of the slot.

        The original instruction (where [dst] is written to) is provided so that
        implementations of this function have an opportunity to perform peephole
        optimization of the resulting instruction.
    *)
    val store_to_slot : [Type.basic | `v128] -> Insn.t -> src:Regvar.t -> dst:Regvar.t -> Insn.t

    (** [substitute i f] performs the substitution [f] to [i] on all reigsters/variables
        that count as definitions/uses in the instruction. *)
    val substitute : Insn.t -> (Regvar.t -> Regvar.t) -> Insn.t

    (** Returns the written registers/variables of the instruction, mapped to
        their types. *)
    val writes_with_types : Insn.t -> [Type.basic | `v128] Regvar.Map.t

    (** Pre-assign stack slots before doing register allocation. *)
    module Pre_assign_slots(C : Context_intf.S) : sig
      (** [pre_assign_slots find base i] replaces uses of virtual stack slots in [i]
          with conrete offsets from [base], according to [find].

          This is meant to happen {i before} register allocation (i.e. before spilling
          happens).

          Opportunity is provided here to produce administrative instructions to manage
          references to stack slots in certain operand forms.
      *)
      val assign : (Regvar.t -> int option) -> Regvar.t -> Insn.t -> Insn.t list C.t
    end

    (** [post_assign_slots find base i] replaces uses of virtual stack slots in [i]
        with conrete offsets from [base], according to [find].

        This is meant to happen {i after} register allocation, where the only
        remaining variables in the program are those referring to spill slots.
    *)
    val post_assign_slots : (Regvar.t -> int option) -> Regvar.t -> Insn.t -> Insn.t

    (** Create a function prologue with no stack frame, given the callee-save
        registers in use and the size of the local variables. *)
    val no_frame_prologue : Reg.t list -> int -> Insn.t list

    (** Create a function epilogue with no stack frame, given the callee-save
        registers in use and the size of the local variables. *)
    val no_frame_epilogue : Reg.t list -> int -> Insn.t list

    (** Create a function prologue with a stack frame, given the callee-save
        registers in use and the size of the local variables. *)
    val frame_prologue : Reg.t list -> int -> Insn.t list

    (** Create a function epilogue with a stack frame, given the callee-save
        registers in use and the size of the local variables. *)
    val frame_epilogue : Reg.t list -> int -> Insn.t list
  end

  module Peephole : sig
    (** Runs target-specific peephole optimizations on a function. *)
    val run : (Insn.t, Reg.t) Pseudo.func -> (Insn.t, Reg.t) Pseudo.func
  end

  (** Emitting the assembly for the target platform.

      This exists separately from the usual pretty-printing facilities because
      the final assembly code may be platform/target specific (i.e. a specific
      assembler is being targeted with a specific syntax).

      The implementation of this module should handle all formatting, such as
      indentation and newlines.
  *)
  module Emit : sig
    (** Emit a prelude of directives for the program, given the name of the
        current module. *)
    val emit_prelude : Format.formatter -> string -> unit

    (** Emit a structure of data. *)
    val emit_data : Format.formatter -> Virtual.data -> unit

    (** Emit the start of a function.

        The name of the function and the linkage are provided.
    *)
    val emit_func : Format.formatter -> (string * Linkage.t) -> unit

    (** Emit the start of a basic block. *)
    val emit_blk : Format.formatter -> Label.t -> unit

    (** Emit an instruction as part of a basic block.

        The label of the instruction, the instruction itself, and the section
        of the containing function are provided. In the case that the section
        is [None], then it will be the default section for code (this is decided
        by the implementation).
    *)
    val emit_insn : Format.formatter -> (Label.t * Insn.t * string option) -> unit

    (** Emit a separator (such as newlines) between data and function elements. *)
    val emit_separator : Format.formatter -> unit -> unit
  end
end
