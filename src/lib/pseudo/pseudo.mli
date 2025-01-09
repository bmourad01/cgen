(** A pseudo-assembly program. *)

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

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type 'a blk = 'a Blk.t [@@deriving bin_io, compare, equal, sexp]

(** A function. *)
module Func : sig
  type 'a t [@@deriving bin_io, compare, equal, sexp]

  (** Construct a functiom. *)
  val create : name:string -> blks:'a blk list -> 'a t

  (** The name of the function. *)
  val name : 'a t -> string

  (** The blocks of the function. *)
  val blks : ?rev:bool -> 'a t -> 'a blk seq

  (** Returns a mapping from labels to blocks of the function. *)
  val map_of_blks : 'a t -> 'a blk Label.Tree.t

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type 'a func = 'a Func.t [@@deriving bin_io, compare, equal, sexp]

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
  val create : dests:('a -> Label.Set.t) -> 'a func -> t
end

(** Liveness analysis of a function. *)
module Live(M : Machine_intf.S) : Live_intf.S
  with type var := M.Regvar.t
   and type var_comparator := M.Regvar.Set.Elt.comparator_witness
   and type func := M.Insn.t func
   and type blk := M.Insn.t blk
   and type cfg := Cfg.t
