open Core
open Regular.Std

module type S = sig
  type t [@@deriving bin_io, compare, equal, sexp]
  type op
  type insn
  type ctrl
  type var
  type var_comparator

  (** Creates a basic block. *)
  val create :
    ?dict:Dict.t ->
    ?args:var list ->
    ?insns:insn list ->
    label:Label.t ->
    ctrl:ctrl ->
    unit ->
    t

  (** Returns the label of the basic block. *)
  val label : t -> Label.t

  (** Returns the arguments of the basic block. *)
  val args : ?rev:bool -> t -> var seq

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
  val liveness : t -> (var, var_comparator) Set.t Label.Tree.t * (var, var_comparator) Set.t

  (** Equivalent to [snd (liveness blk)]. *)
  val free_vars : t -> (var, var_comparator) Set.t

  (** [uses_var b x] returns [true] if the variable [x] appears in the
      free variables of [b].

      Equivalent to [Set.mem (free_vars b) x].
  *)
  val uses_var : t -> var -> bool

  (** [defines_var b x] returns [true] if the variable [x] is defined
      in the block [b]. *)
  val defines_var : t -> var -> bool

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
  val map_args : t -> f:(var -> var) -> t

  (** [map_insns b ~f] returns [b] with each data instruction applied
      to [f]. *)
  val map_insns : t -> f:(Label.t -> op -> op) -> t

  (** [map_ctrl b ~f] returns [b] with the terminator applied to [f]. *)
  val map_ctrl : t -> f:(ctrl -> ctrl) -> t

  (** [prepend_arg b a ?before] prepends the argument [a] to the block

      If [before] is [None], then [a] is inserted at the beginning of
      the argument list.

      If [before] is [Some x], then [a] will appear directly before the
      argument [x]. If [x] doesn't exist, then [a] is not inserted.
  *)
  val prepend_arg : ?before:var -> t -> var -> t

  (** [append_arg b a ?after] appends the argument [a] to the block [b].

      If [after] is [None], then [a] is inserted at the end of the
      argument list.

      If [after] is [Some x], then [a] will appear directly after the
      argument [x]. If [x] doesn't exist, then [a] is not inserted.
  *)
  val append_arg : ?after:var -> t -> var -> t

  (** [prepend_insn b d ?before] prepends the data instruction [d] to
      the block [b].

      If [before] is [None], then [d] is inserted at the beginning of
      the data instructions.

      If [before] is [Some l], then [d] will appear directly before the
      data instruction at label [l]. If [l] doesn't exist, then [d] is
      not inserted.
  *)
  val prepend_insn : ?before:Label.t -> t -> insn -> t

  (** [append_insn b d ?after] appends the data instruction [d] to
      the block [b].

      If [after] is [None], then [d] is inserted at the end of the
      data instructions.

      If [after] is [Some l], then [d] will appear directly after the
      data instruction at label [l]. If [l] doesn't exist, then [d] is
      not inserted.
  *)
  val append_insn : ?after:Label.t -> t -> insn -> t

  (** Similar to [prepend_insn], but for a list of instructions.

      Note that the instructions are prepended to [before] starting
      with the last instruction.
  *)
  val prepend_insns : ?before:Label.t -> t -> insn list -> t

  (** Similar to [append_insn], but for a list of instructions.

      Note that the instructions are appended to [after] starting
      with the first instruction.
  *)
  val append_insns : ?after:Label.t -> t -> insn list -> t

  (** Replaces the control-flow instruction in the block. *)
  val with_ctrl : t -> ctrl -> t

  (** Replaces the instructions of the block. *)
  val with_insns : t -> insn list -> t

  (** [remove_arg b x] removes an argument [x] from the block [b],
      if it exists. *)
  val remove_arg : t -> var -> t

  (** [remove_insn b l] removes a data instruction with label [l] from
      the block [b], if it exists. *)
  val remove_insn : t -> Label.t -> t

  (** [has_arg b x] returns true if [b] has an argument [x]. *)
  val has_arg : t -> var -> bool

  (** [has_lhs b x] returns [true] if a data instruction in [b] defines
      [x]. *)
  val has_lhs : t -> var -> bool

  include Regular.S with type t := t
end
