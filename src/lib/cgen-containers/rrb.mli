(** RRB (Relaxed-Radix-Balanced) vectors. *)

(** A vector. *)
type 'a t [@@deriving bin_io, equal, compare, sexp]

exception Out_of_bounds

(** The empty vector. *)
val empty : 'a t

(** Constructs a singleton vector. *)
val singleton : 'a -> 'a t

(** Returns the number of elements in the vector. *)
val length : 'a t -> int

(** Returns [true] if the vector has no elements. *)
val is_empty : 'a t -> bool

(** [get t i] gets the element at index [i] in [t].

    If [i] is within the bounds of [t], then [Some x] is
    returned, where [x] is the element at index [i].

    Otherwise, [None] is returned.
*)
val get : 'a t -> int -> 'a option

(** Exceptional version of [get].

    @raise Out_of_bounds if the index is out of bounds
*)
val get_exn : 'a t -> int -> 'a

(** [set t i x] sets the element at index [i] in [t] to [x].

    If [i] is out of bounds, [t] is returned unmodified.
*)
val set : 'a t -> int -> 'a -> 'a t

(** Same as [set], but transforms the element at [i] via [f]. *)
val update : 'a t -> int -> f:('a -> 'a) -> 'a t

(** Transforms each element in the vector according to [f]. *)
val map : 'a t -> f:('a -> 'b) -> 'b t

(** Applies [f] to each element, left to right. *)
val iter : 'a t -> f:('a -> unit) -> unit

(** Applies [f] to each element, right to left. *)
val iter_rev : 'a t -> f:('a -> unit) -> unit

(** Returns [true] if [f] holds for at least one element (short-circuits). *)
val exists : 'a t -> f:('a -> bool) -> bool

(** Returns the first element for which [f] holds, if any (short-circuits). *)
val find : 'a t -> f:('a -> bool) -> 'a option

(** Returns the index of the first element for which [f] holds, if any
    (short-circuits). *)
val find_index : 'a t -> f:('a -> bool) -> int option

(** Returns the vector of elements for which [f] holds, in order. *)
val filter : 'a t -> f:('a -> bool) -> 'a t

(** Applies [f] to each element, keeping the [Some] results, in order. *)
val filter_map : 'a t -> f:('a -> 'b option) -> 'b t

(** Accumulates a value from left-to-right for each element
    in the vector, according to [f], with the initial value
    [init]. *)
val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b

(** Same as [fold], but also provides index of the element to [f]. *)
val foldi : 'a t -> init:'b -> f:(int -> 'b -> 'a -> 'b) -> 'b

(** Same as [fold], but accumulates right-to-left. *)
val fold_right : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b

(** Converts the vector to a list. *)
val to_list : 'a t -> 'a list

(** Converts the vector to a list in reverse order. *)
val to_list_rev : 'a t -> 'a list

(** Converts the list into a vector. *)
val of_list : 'a list -> 'a t

(** [init n ~f] constructs a vector of length [n] (or the empty vector if
    [n <= 0]) whose element at index [i] is [f i]. *)
val init : int -> f:(int -> 'a) -> 'a t

(** Builds a vector from a sequence, without an intermediate list. *)
val of_sequence : 'a Base.Sequence.t -> 'a t

(** Converts the vector to a sequence. *)
val to_sequence : 'a t -> 'a Base.Sequence.t

(** Converts the vector to a sequence in reverse order. *)
val to_sequence_rev : 'a t -> 'a Base.Sequence.t

(** [take t n] returns [t] with its first [n] elements,
    discarding the rest.

    If [n <= 0], the empty vector is returned.

    If [n >= length t], the vector [t] is returned unchanged.
*)
val take : 'a t -> int -> 'a t

(** [drop t n] returns [t] with its first [n] elements
    discarded.

    If [n <= 0], the vector [t] is returned unchanged.

    If [n >= length t], the empty vector is returned.
*)
val drop : 'a t -> int -> 'a t

(** [split_at t n] is equivalent to [(take t n, drop t n)] *)
val split_at : 'a t -> int -> 'a t * 'a t

(** [cons x t] prepends [x] to [t]. *)
val cons : 'a -> 'a t -> 'a t

(** [snoc t x] appends [x] to [t]. *)
val snoc : 'a t -> 'a -> 'a t

(** [append t1 t2] concatenates [t1] and [t2]. *)
val append : 'a t -> 'a t -> 'a t

(** [insert_before t xs ~f] splices [xs] in immediately before the first
    element of [t] satisfying [f], or returns [t] unchanged if none does. *)
val insert_before : 'a t -> 'a t -> f:('a -> bool) -> 'a t

(** As {!insert_before}, but immediately after the matching element. *)
val insert_after : 'a t -> 'a t -> f:('a -> bool) -> 'a t
