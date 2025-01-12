(** A pseudo-assembly program. *)

open Core
open Regular.Std

(** A container for a pseudo-assembly instruction. *)
module Insn : sig
  type 'a t [@@deriving bin_io, compare, equal, sexp]

  (** Create the instruction with a given label. *)
  val create : label:Label.t -> insn:'a -> 'a t

  (** The label of the instruction. *)
  val label : 'a t -> Label.t

  (** The instruction itself. *)
  val insn : 'a t -> 'a
end

type 'a insn = 'a Insn.t [@@deriving bin_io, compare, equal, sexp]

(** A block of instructions. *)
module Blk : sig
  type 'a t [@@deriving bin_io, compare, equal, sexp]

  (** Construct a block. *)
  val create : label:Label.t -> insns:'a insn list -> 'a t

  (** The label of the block. *)
  val label : 'a t -> Label.t

  (** The instructions of the block. *)
  val insns : ?rev:bool -> 'a t -> 'a insn seq

  (** Returns [true] if the block has the given label. *)
  val has_label : 'a t -> Label.t -> bool

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

  type ('a, 'b) t [@@deriving bin_io, compare, equal, sexp]

  (** The label of the entry block. *)
  val entry : ('a, 'b) t -> Label.t

  (** Construct a function.

      [dict]: function attributes

      [name]: the function name

      [blks]: the basic blocks of the function

      [rets]: the registers returned by the function

      @raise Invalid_argument if [blks] is empty.
  *)
  val create_exn :
    ?dict:Dict.t ->
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

  (** Returns a mapping from labels to blocks of the function. *)
  val map_of_blks : ('a, 'b) t -> 'a blk Label.Tree.t

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

  val pp :
    (Format.formatter -> 'a -> unit) ->
    (Format.formatter -> 'b -> unit) ->
    Format.formatter ->
    ('a, 'b) t -> unit
end

type ('a, 'b) func = ('a, 'b) Func.t [@@deriving bin_io, compare, equal, sexp]

(** The control-flow graph of the function. *)
module Cfg : sig
  include Label.Graph

  (** Creates the control-flow graph.

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
  val create : dests:('a -> Label.Set.t) -> ('a, 'b) func -> t
end

(** Liveness analysis of a function. *)
module Live(M : Machine_intf.S) : Live_intf.S
  with type var := M.Regvar.t
   and type var_comparator := M.Regvar.Set.Elt.comparator_witness
   and type func := (M.Insn.t, M.Reg.t) func
   and type blk := M.Insn.t blk
   and type cfg := Cfg.t

(** Removes instructions whose results are never used. *)
module Remove_dead_insns(M : Machine_intf.S) : sig
  val run : (M.Insn.t, M.Reg.t) func -> (M.Insn.t, M.Reg.t) func
end
