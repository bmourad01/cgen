(** A pseudo-assembly program. *)

open Core
open Regular.Std

(** A container for a pseudo-assembly instruction. *)
module Insn : sig
  (** An instruction descriptor, where ['a] is the concrete type
      of instructions. *)
  type 'a t [@@deriving bin_io, compare, equal, sexp]

  (** Create the instruction with a given label. *)
  val create : label:Label.t -> insn:'a -> 'a t

  (** The label of the instruction. *)
  val label : 'a t -> Label.t

  (** The instruction itself. *)
  val insn : 'a t -> 'a

  (** Replaces the instruction. *)
  val with_insn : 'a t -> 'a -> 'a t

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type 'a insn = 'a Insn.t [@@deriving bin_io, compare, equal, sexp]

(** A block of instructions. *)
module Blk : sig
  (** A basic block, where ['a] is the concrete type of instructions. *)
  type 'a t [@@deriving bin_io, compare, equal, sexp]

  (** Construct a block. *)
  val create : label:Label.t -> insns:'a insn list -> 'a t

  (** The label of the block. *)
  val label : 'a t -> Label.t

  (** The instructions of the block. *)
  val insns : ?rev:bool -> 'a t -> 'a insn seq

  (** Returns [true] if the block has the given label. *)
  val has_label : 'a t -> Label.t -> bool

  (** Transforms the instructions of the block according to [f]. *)
  val map_insns : 'a t -> f:('a insn -> 'a insn) -> 'a t

  (** Replaces the instructions of the block. *)
  val with_insns : 'a t -> 'a insn list -> 'a t

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type 'a blk = 'a Blk.t [@@deriving bin_io, compare, equal, sexp]

(** A function. *)
module Func : sig
  (** Pre-defined attributes. *)
  module Tag : sig
    (** The function needs a stack frame set up. *)
    val needs_stack_frame : unit Dict.tag
  end

  (** The type of a pseudo-assembly function, where ['a] is the type of
      instructions, and ['b] is the type of registers. *)
  type ('a, 'b) t [@@deriving bin_io, compare, equal, sexp]

  (** The label of the entry block. *)
  val entry : ('a, 'b) t -> Label.t

  (** Construct a function.

      [dict]: function attributes

      [slots]: stack slots

      [name]: the function name

      [blks]: the basic blocks of the function

      [rets]: the registers returned by the function

      @raise Invalid_argument if [blks] is empty.
  *)
  val create_exn :
    ?dict:Dict.t ->
    ?slots:Virtual.slot list ->
    name:string ->
    blks:'a blk list ->
    rets:'b list ->
    unit ->
    ('a, 'b) t

  (** Construct a function.

      Returns [Error _] if [blks] is empty.
  *)
  val create :
    ?dict:Dict.t ->
    ?slots:Virtual.slot list ->
    name:string ->
    blks:'a blk list ->
    rets:'b list ->
    unit ->
    ('a, 'b) t Or_error.t

  (** The name of the function. *)
  val name : ('a, 'b) t -> string

  (** The blocks of the function. *)
  val blks : ?rev:bool -> ('a, 'b) t -> 'a blk seq

  (** The return registers of the function. *)
  val rets : ?rev:bool -> ('a, 'b) t -> 'b seq

  (** The attributes of the function. *)
  val dict : ('a, 'b) t -> Dict.t

  (** The stack slots of the function. *)
  val slots : ?rev:bool -> ('a, 'b) t -> Virtual.slot seq

  (** Returns the label of the entry block. *)
  val start : ('a, 'b) t -> Label.t

  (** Returns the linkage of the function. *)
  val linkage : ('a, 'b) t -> Linkage.t

  (** Returns [true] if the function has the specified name. *)
  val has_name : ('a, 'b) t -> string -> bool

  (** Returns a mapping from labels to blocks of the function. *)
  val map_of_blks : ('a, 'b) t -> 'a blk Label.Tree.t

  (** Replaces the dictionary of the function. *)
  val with_dict : ('a, 'b) t -> Dict.t -> ('a, 'b) t

  (** Replaces the slots of the function. *)
  val with_slots : ('a, 'b) t -> Virtual.slot list -> ('a, 'b) t

  (** Transforms the blocks of the function according to [f]. *)
  val map_blks : ('a, 'b) t -> f:('a blk -> 'a blk) -> ('a, 'b) t

  (** Replaces the blocks of the function. *)
  val with_blks : ('a, 'b) t -> 'a blk list -> ('a, 'b) t

  (** Appends a slot to the function. *)
  val insert_slot : ('a, 'b) t -> Virtual.slot -> ('a, 'b) t

  (** Same as [insert_slot], but for a list of slots. *)
  val insert_slots : ('a, 'b) t -> Virtual.slot list -> ('a, 'b) t

  (** [update_blk fn b] returns [fn] with block [b] updated, if it exists. *)
  val update_blk : ('a, 'b) t -> 'a blk -> ('a, 'b) t

  (** Same as [update_blk], but for a list of blocks for updating in batches,
      which should be more efficient.

      @raise Invalid_argument if the list of blocks contains duplicate labels.
  *)
  val update_blks_exn : ('a, 'b) t -> 'a blk list -> ('a, 'b) t

  (** Same as [update_blks_exn], but returns an error if there is a duplicate
      block label. *)
  val update_blks : ('a, 'b) t -> 'a blk list -> ('a, 'b) t Or_error.t

  (** Same as [update_blks], but accepts a mapping from labels to blocks.

      Note that this does not enforce that the keys of the map are the
      same as the label of each corresponding block.
  *)
  val update_blks' : ('a, 'b) t -> 'a blk Label.Tree.t -> ('a, 'b) t

  (** Returns a mapping from block labels to their immediate next block
      in the sequence.

      This can be useful for identifying which blocks can potentially
      fall through to another block.
  *)
  val collect_afters : ('a, 'b) t -> Label.t Label.Tree.t

  (** [remove_blk_exn fn l] removes the block with label [l] from function
      [f].

      @raise Invalid_argument if [l] is the label of the entry block.
  *)
  val remove_blk_exn : ('a, 'b) t -> Label.t -> ('a, 'b) t

  (** Same as [remove_blk_exn], but removes multiple blocks.

      @raise Invalid_argument if one of the labels is the entry block.
  *)
  val remove_blks_exn : ('a, 'b) t -> Label.t list -> ('a, 'b) t

  val pp :
    (Format.formatter -> 'a -> unit) ->
    (Format.formatter -> 'b -> unit) ->
    Format.formatter ->
    ('a, 'b) t -> unit
end

type ('a, 'b) func = ('a, 'b) Func.t [@@deriving bin_io, compare, equal, sexp]

(** A module. *)
module Module : sig
  type ('a, 'b) t [@@deriving bin_io, compare, equal, sexp]

  val create :
    ?dict:Dict.t ->
    ?data:Virtual.data list ->
    ?funs:('a, 'b) func list ->
    name:string ->
    unit ->
    ('a, 'b) t

  (** The name of the module. *)
  val name : ('a, 'b) t -> string

  (** Structs defined in the module. *)
  val data : ?rev:bool -> ('a, 'b) t -> Virtual.data seq

  (** Functions defined in the module. *)
  val funs : ?rev:bool -> ('a, 'b) t -> ('a, 'b) func seq

  (** Returns the dictionary of the module. *)
  val dict : ('a, 'b) t -> Dict.t

  (** Replaces the dictionary of the module. *)
  val with_dict : ('a, 'b) t -> Dict.t -> ('a, 'b) t

  (** [with_tag m t v] binds [v] to tag [t] in the dictionary of [m]. *)
  val with_tag : ('a, 'b) t -> 'a Dict.tag -> 'a -> ('a, 'b) t

  (** Returns [true] if the module has the associated name. *)
  val has_name : ('a, 'b) t -> string -> bool

  (** Appends a struct to the module. *)
  val insert_data : ('a, 'b) t -> Virtual.data -> ('a, 'b) t

  (** Appends a function to the module. *)
  val insert_fn : ('a, 'b) t -> ('a, 'b) func -> ('a, 'b) t

  (** Removes the struct associated with the name. *)
  val remove_data : ('a, 'b) t -> string -> ('a, 'b) t

  (** Removes the function associated with the name. *)
  val remove_fn : ('a, 'b) t -> string -> ('a, 'b) t

  (** Returns the module with each struct transformed by [f]. *)
  val map_data : ('a, 'b) t -> f:(Virtual.data -> Virtual.data) -> ('a, 'b) t

  (** Returns the module with each function transformed by [f]. *)
  val map_funs : ('a, 'b) t -> f:(('a, 'b) func -> ('a, 'b) func) -> ('a, 'b) t

  (** Replaces the functions in the module. *)
  val with_funs : ('a, 'b) t -> ('a, 'b) func list -> ('a, 'b) t

  (** Returns the module with each struct transformed by [f],
      where [f] may fail. *)
  val map_data_err :
    ('a, 'b) t ->
    f:(Virtual.data -> Virtual.data Or_error.t) ->
    ('a, 'b) t Or_error.t

  (** Returns the module with each function transformed by [f],
      where [f] may fail. *)
  val map_funs_err :
    ('a, 'b) t ->
    f:(('a, 'b) func -> ('a, 'b) func Or_error.t) ->
    ('a, 'b) t Or_error.t

  val pp :
    (Format.formatter -> 'a -> unit) ->
    (Format.formatter -> 'b -> unit) ->
    Format.formatter ->
    ('a, 'b) t ->
    unit
end

type ('a, 'b) module_ = ('a, 'b) Module.t [@@deriving bin_io, compare, equal, sexp]

(** The control-flow graph of the function. *)
module Cfg : sig
  include Label.Graph_s

  (** Creates the control-flow graph.

      [is_barrier] indicates if a function has no implicit fallthrough. See
      then interface provided by [Machine_intf.S].

      [dests] is the set of static control-flow destinations of a given
      instruction. See the interface provided by [Machine_intf.S].

      Each node of the graph is the label of a basic block in the function,
      and edges between basic blocks correspond to control-flow transfers
      between them.

      Additionally, two pseudo-labels are added to the graph ([Label.pseudoentry]
      and [Label.pseudoexit]). These labels link with each "entry" and "exit"
      node in the function, respectively. This representation is useful for
      computing the dominator tree of the function in question.
  *)
  val create :
    is_barrier:('a -> bool) ->
    dests:('a -> Label.Set.t) ->
    ('a, 'b) func -> t
end
