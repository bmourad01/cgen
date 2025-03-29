(** The main interface for target machine implementations. *)

open Core
open Regular.Std

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

  (** A machine register. *)
  module Reg : sig
    type t [@@deriving bin_io, compare, equal, hash, sexp]

    (** Stack pointer register. *)
    val sp : t

    (** Frame pointer register. *)
    val fp : t

    (** Designated "scratch" register.

        This should be a general purpose register, which will never be chosen
        for register allocation, but instead used to hold the results of
        intermediate computations.
    *)
    val scratch : t

    (** Same as [scratch], but for floating-point registers. *)
    val scratch_fp : t

    (** A list of all general purpose registers, in order of their preference
        for register allocation, {b except for} [scratch], which {b must not}
        be contained. *)
    val allocatable : t list

    (** A list of all floating point registers, in order of their preference
        for register allocation, {b except for} [scratch_fp], which {b must not}
        be contained. *)
    val allocatable_fp : t list

    (** Returns the class of the register. *)
    val classof : t -> [`gpr | `fp]

    (** The type of the register. *)
    val typeof : t -> [Type.basic | `v128]

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

  (** A machine register or a virtual variable.

      To ease implementation of the backend, instructions can refer to
      both registers and variables after instruction selection. After
      register allocation, it is expected that no variables will be
      present.
  *)
  module Regvar : sig
    type t

    val reg : Reg.t -> t
    val var : [`gpr | `fp] -> Var.t -> t
    val is_reg : t -> bool
    val is_var : t -> bool
    val which : t -> (Reg.t, Var.t * [`gpr | `fp]) Either.t

    include Regular.S with type t := t
  end

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

    (** Pretty-prints the instruction. *)
    val pp : Format.formatter -> t -> unit
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
    val copy : Insn.t -> (Regvar.t * Regvar.t) option

    (** Produce an instruction to load a value from a slot, where [src] holds the
        address of the slot and [dst] is destination register/variable. *)
    val load_from_slot : [Type.basic | `v128] -> dst:Regvar.t -> src:Regvar.t -> Insn.t

    (** Produce an instruction to store a value to a slot, where [src] holds the
        value being stored and [dst] is the address of the slot. *)
    val store_to_slot : [Type.basic | `v128] -> src:Regvar.t -> dst:Regvar.t -> Insn.t

    (** [substitute i f] performs the substitution [f] to [i] on all reigsters/variables
        that count as definitions/uses in the instruction. *)
    val substitute : Insn.t -> (Regvar.t -> Regvar.t) -> Insn.t

    (** Returns the written registers/variables of the instruction, mapped to
        their types. *)
    val writes_with_types : Insn.t -> [Type.basic | `v128] Regvar.Map.t
  end
end
