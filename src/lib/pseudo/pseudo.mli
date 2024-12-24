(** A pseudo-assembly program. *)

open Regular.Std

(** A block of instructions. *)
module Blk : sig
  type 'a t [@@deriving bin_io, compare, equal, sexp]

  (** Construct a block. *)
  val create : label:Label.t -> insns:'a list -> 'a t

  (** The label of the block. *)
  val label : 'a t -> Label.t

  (** The instructions of the block. *)
  val insns : ?rev:bool -> 'a t -> 'a seq

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

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

type 'a func = 'a Func.t [@@deriving bin_io, compare, equal, sexp]
