open Regular.Std

(** Loop analysis of a function. *)
module type S = sig
  type func

  (** The identifier of a loop. *)
  type loop [@@deriving compare, equal]

  (** The loop nesting level. *)
  type level = private int [@@deriving compare, equal]

  (** The loop data. *)
  type data

  (** The loop analysis. *)
  type t

  val pp : Format.formatter -> t -> unit

  (** [header d] gets the header block of the loop. *)
  val header : data -> Label.t

  (** [parent d] gets the parent loop, if it exists. *)
  val parent : data -> loop option

  (** [level d] gets the nesting level of the loop. *)
  val level : data -> level

  (** [analyze fn] performs the loop analysis of [fn]. *)
  val analyze : func -> t

  (** [get t x] returns the data for loop [x].

      @raise Invalid_argument is [x] does not exist in the function.
  *)
  val get : t -> loop -> data

  (** [blk t l] returns the innermost loop for the block
      at label [l], if it exists. *)
  val blk : t -> Label.t -> loop option

  (** [mem t l] returns [true] if the block at label [l] is
      part of a loop. *)
  val mem : t -> Label.t -> bool

  (** [is_header t l] returns [true] if the block at label [l]
      is the header of a loop. *)
  val is_header : t -> Label.t -> bool

  (** [is_child_of ~parent t n] returns [true] if [equal_loop n parent]
      or [n] is nested in [parent]. *)
  val is_child_of : parent:loop -> t -> loop -> bool

  (** [is_in_loop t l n] returns [true] if the block at label [l] is
      a member of the loop [n]. *)
  val is_in_loop : t -> Label.t -> loop -> bool

  (** [loops_of t l] returns the sequence of loops that the block at
      label [l] is within, starting from the innermost loop. *)
  val loops_of : t -> Label.t -> loop seq

  val pp_loop : Format.formatter -> loop -> unit
  val pp_level : Format.formatter -> level -> unit
  val pp_data : Format.formatter -> data -> unit
end
