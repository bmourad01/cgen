open Core
open Regular.Std

module type S = sig
  type t [@@deriving bin_io, compare, equal, sexp]
  type blk
  type var
  type argt
  type slot

  (** Creates a function.

      It is assumed that [blks] is ordered such that the entry block is
      the first element.

      @raise Invalid_argument if [blks] is empty.
  *)
  val create_exn :
    ?dict:Dict.t ->
    ?slots:slot list ->
    name:string ->
    blks:blk list ->
    args:(var * argt) list ->
    unit ->
    t

  (** Same as [create_exn], but returns an error upon failure. *)
  val create :
    ?dict:Dict.t ->
    ?slots:slot list ->
    name:string ->
    blks:blk list ->
    args:(var * argt) list ->
    unit ->
    t Or_error.t

  (** Returns the name of the function. *)
  val name : t -> string

  (** Returns the slots of the function. *)
  val slots : ?rev:bool -> t -> slot seq

  (** Returns the basic blocks of the function. *)
  val blks : ?rev:bool -> t -> blk seq

  (** Returns the label of the entry block. *)
  val entry : t -> Label.t

  (** Returns the arguments of the function, along with their types. *)
  val args : ?rev:bool -> t -> (var * argt) seq

  (** Returns the dictionary of the function. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the function. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag fn t v] binds [v] to tag [t] in the dictionary of [fn]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the function has the associated name. *)
  val has_name : t -> string -> bool

  (** Returns a mapping from block labels to blocks.

      @raise Invalid_argument if there are duplicate labels
  *)
  val map_of_blks : t -> blk Label.Tree.t

  (** [map_blks fn ~f] returns [fn] with each basic block applied to [f].

      Note that [f] is allowed to change the label of the entry block.
      This change is reflected in the updated function.
  *)
  val map_blks : t -> f:(blk -> blk) -> t

  (** Same as [map_blks], but handles the case where [f] may fail. *)
  val map_blks_err : t -> f:(blk -> blk Or_error.t) -> t Or_error.t

  (** Appends a block to the end of the function. *)
  val insert_blk : t -> blk -> t

  (** Appends a slot to the function. *)
  val insert_slot : t -> slot -> t

  (** Removes a slot from the function that corresponds to the given var. *)
  val remove_slot : t -> Var.t -> t

  (** [remove_blk_exn fn l] removes the block with label [l] from function
      [f].

      @raise Invalid_argument if [l] is the label of the entry block.
  *)
  val remove_blk_exn : t -> Label.t -> t

  (** Same as [remove_blk_exn], but returns an error upon failure. *)
  val remove_blk : t -> Label.t -> t Or_error.t

  (** Same as [remove_blk_exn], but removes multiple blocks.

      @raise Invalid_argument if one of the labels is the entry block.
  *)
  val remove_blks_exn : t -> Label.t list -> t

  (** Same as [remove_blks_exn], but returns an error if one of the labels
      is the entry block. *)
  val remove_blks : t -> Label.t list -> t Or_error.t

  (** [prepend_arg ?before fn x t] adds the argument [x] of type [t] to [fn].

      If [before] is [None], then [x] is inserted at the beginning of the
      argument list.

      If [before] is [Some y], then [x] will appear directly before the
      argument [y]. If [y] doesn't exist, then [x] is not inserted.
  *)
  val prepend_arg : ?before:var -> t -> var -> argt -> t

  (** [append_arg ?after fn x t] adds the argument [x] of type [t] to [fn].

      If [after] is [None], then [x] is inserted at the end of the
      argument list.

      If [after] is [Some y], then [x] will appear directly after the
      argument [y]. If [y] doesn't exist, then [x] is not inserted.
  *)
  val append_arg : ?after:var -> t -> var -> argt -> t

  (** [remove_arg fn x] removes the argument [x] from [fn], if it exists. *)
  val remove_arg : t -> var -> t

  (** Returns [true] if the function has a block associated with the given
      label. *)
  val has_blk : t -> Label.t -> bool

  (** Finds the block with the associated label, if it exists. *)
  val find_blk : t -> Label.t -> blk option

  (** Returns the next block (after the given label) if it exists. *)
  val next_blk : t -> Label.t -> blk option

  (** Returns the previous block (before the given label) if it exists. *)
  val prev_blk : t -> Label.t -> blk option

  (** [update_blk_exn fn b] returns [fn] with block [b] updated, if it exists. *)
  val update_blk : t -> blk -> t

  (** Same as [update_blk], but for a list of blocks for updating in batches,
      which should be more efficient.

      @raise Invalid_argument if the list of blocks contains duplicate labels.
  *)
  val update_blks_exn : t -> blk list -> t

  (** Same as [update_blks_exn], but returns an error if there is a duplicate
      block label. *)
  val update_blks : t -> blk list -> t Or_error.t

  include Regular.S with type t := t
end
