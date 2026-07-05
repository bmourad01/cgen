(** A finger tree data structure.

    This is used to efficiently represent a sequence where
    both the beginning and end can be accessed in constant
    time. Additionally, appending and splitting sequences
    is done in logarithmic time.
*)

open Regular.Std

type 'a t [@@deriving bin_io, compare, equal, sexp]

(** Returns the last element of the sequence.

    Raises [Invalid_argument] if the sequence is empty.
*)
val last_exn : 'a t -> 'a

(** Returns the first element of the sequence.

    Raises [Invalid_argument] if the sequence is empty.
*)
val head_exn : 'a t -> 'a

(** Like {!last_exn}, but returns [None] on failure. *)
val last : 'a t -> 'a option

(** Like {!head_exn}, but returns [None] on failure. *)
val head : 'a t -> 'a option

(** Constructs a single-element sequence. *)
val singleton : 'a -> 'a t

(** The empty sequence. *)
val empty : 'a t

(** Returns [true] if the sequence is empty. *)
val is_empty : 'a t -> bool

(** Accumulate a value from start-to-end. *)
val fold_left : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b

(** Accumulate a value from end-to-start. *)
val fold_right : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b

(** Alias for {!fold_left}. *)
val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b

(** Apply [f] to each element from start-to-end. *)
val iter : 'a t -> f:('a -> unit) -> unit

(** Apply [f] to each element from end-to-start. *)
val iter_rev : 'a t -> f:('a -> unit) -> unit

(** Transform each element of the sequence according to [f]. *)
val map : 'a t -> f:('a -> 'b) -> 'b t

(** Same as {!map}, but the resulting sequence is reversed. *)
val map_rev : 'a t -> f:('a -> 'b) -> 'b t

(** Construct a sequence from a list. *)
val of_list : 'a list -> 'a t

(** Construct a reversed sequence from a list. *)
val of_list_rev : 'a list -> 'a t

(** Prepend an element to the sequence. *)
val cons : 'a t -> 'a -> 'a t

(** Append an element to the sequence. *)
val snoc : 'a t -> 'a -> 'a t

(** Returns the sequence with the last element removed, along
    with the element itself, or [None] if the sequence is empty. *)
val rear : 'a t -> ('a t * 'a) option

(** Returns the sequence with the first element removed, along
    with the element itself, or [None] if the sequence is empty. *)
val front : 'a t -> ('a t * 'a) option

(** Same as {!front}, but discards the first element. *)
val tail : 'a t -> 'a t option

(** Same as {!rear}, but discards the last element. *)
val init : 'a t -> 'a t option

(** Same as {!rear}, but raises [Invalid_argument] if the sequence
    is empty. *)
val rear_exn : 'a t -> 'a t * 'a

(** Same as {!front}, but raises [Invalid_argument] if the sequence
    is empty. *)
val front_exn : 'a t -> 'a t * 'a

(** Same as {!tail}, but raises [Invalid_argument] if the sequence
    is empty. *)
val tail_exn : 'a t -> 'a t

(** Same as {!init}, but raises [Invalid_argument] if the sequence
    is empty. *)
val init_exn : 'a t -> 'a t

(** Reverses the sequence. *)
val reverse : 'a t -> 'a t

(** Splits the sequence at the first index satisfying [f]. *)
val split : 'a t -> f:(int -> bool) -> 'a t * 'a t

(** Returns the number of elements in the sequence. *)
val length : 'a t -> int

(** [append a b] appends [b] to the end of [a]. *)
val append : 'a t -> 'a t -> 'a t

(** Splits the sequence at the provided index.

    Raises [Invalid_argument] if the index is out-of-bounds.
*)
val split_at_exn : 'a t -> int -> 'a t * 'a t

(** Same as {!split_at_exn}, but returns [None] on failure. *)
val split_at : 'a t -> int -> ('a t * 'a t) option

(** Returns the first element at the index satisfying [f].

    Raises [Invalid_argument] if the element is not found.
*)
val lookup_exn : 'a t -> f:(int -> bool) -> 'a 

(** Same as {!lookup}, but returns [None] on failure. *)
val lookup : 'a t -> f:(int -> bool) -> 'a option

(** Returns the element at the provided index.

    Raises [Invalid_argument] if the index is out-of-bounds.
*)
val get_exn : 'a t -> int -> 'a

(** Same as {!get_exn}, but returns [None] on failure. *)
val get : 'a t -> int -> 'a option

(** [set t i x] replaces the element in [t] at index [i] with [x].

    Raises [Invalid_argument] if the index is out-of-bounds.
*)
val set : 'a t -> int -> 'a -> 'a t

(** [update t i ~f] is like {!map}, but only applied to the
    element at index [i].

    Raises [Invalid_argument] if the index is out-of-bounds.
*)
val update : 'a t -> int -> f:('a -> 'a) -> 'a t

(** Compares two sequences according to [compare]. *)
val compare : 'a t -> 'a t -> compare:('a -> 'a -> int) -> int

(** Tests two sequences for equality according to [equal]. *)
val equal : 'a t -> 'a t -> equal:('a -> 'a -> bool) -> bool

(** [insert t x i] inserts [x] into [t] at element [i].

    If [i <= 0], then this function is equivalent to {!cons}.
    If [i >= length t], then this function is equivalent to {!snoc}.
*)
val insert : 'a t -> 'a -> int -> 'a t

(** Removes all elements not satisfying [f]. *)
val filter : 'a t -> f:('a -> bool) -> 'a t

(** Returns a lazy stream of all elements.

    If [rev] is true, then the sequence is reversed.
*)
val enum : ?rev:bool -> 'a t -> 'a seq

(** Returns the first element satisfying [f], from start-to-end. *)
val find : 'a t -> f:('a -> bool) -> 'a option

(** Same as {!find}, but the index of the element is provded to [f],
    and if a satisfying element is found, the index is part of the
    result. *)
val findi : 'a t -> f:(int -> 'a -> bool) -> (int * 'a) option

(** Returns the index of the first element, from start-to-end,
    that satisfies [f]. *)
val index : 'a t -> f:('a -> bool) -> int option

(** Returns [true] if any element satisfies [f].

    If the sequence is empty, then [false] is returned.
*)
val exists : 'a t -> f:('a -> bool) -> bool

(** Returns the element immediately after the first element
    satisfying [f], from start-to-end. *)
val next : 'a t -> f:('a -> bool) -> 'a option

(** Returns the element immediately before the first element
    satisfying [f], from end-to-start. *)
val prev : 'a t -> f:('a -> bool) -> 'a option

(** [remove t i] removes the element at index [i] from [t].

    If [i] is out-of-bounds, the sequence is returned unchanged.
*)
val remove : 'a t -> int -> 'a t

(** Removes the first element satisfying [f], from start-to-end. *)
val remove_if : 'a t -> f:('a -> bool) -> 'a t

(** [update_if t x ~f] finds the first element, from start-to-end,
    that satisfieds [f]. If found, the element is replaced with [x]. *)
val update_if : 'a t -> 'a -> f:('a -> bool) -> 'a t

(** Converts the sequence as a list. *)
val to_list : 'a t -> 'a list

(** Returns the minimum element satisfying [compare]. *)
val min_elt : 'a t -> compare:('a -> 'a -> int) -> 'a option

(** Returns the maximum element satisfying [compare]. *)
val max_elt : 'a t -> compare:('a -> 'a -> int) -> 'a option

(** Pretty-prints the sequence. *)
val pp :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> unit) ->
  Format.formatter ->
  'a t ->
  unit
