(** A mutable, dynamically-sized array. Not thread-safe. *)

open Core
open Regular.Std

(** The array. *)
type 'a t

(** Creates the array with optional [capacity].

    If [capacity < 1], then the initial capacity is [1].
*)
val create : ?capacity:int -> unit -> 'a t

(** The number of elements currently occupying the array. *)
val length : 'a t -> int

(** Returns [true] if [length t = 0]. *)
val is_empty : 'a t -> bool

(** The number of possible elements that can be held in the array. *)
val capacity : 'a t -> int

(** [ensure_capacity t n] ensures that [t] can hold at least [n]
    elements. *)
val ensure_capacity : 'a t -> int -> unit

(** Returns a unique copy of the array. *)
val copy : 'a t -> 'a t

(** Removes all elements from the array. *)
val clear : 'a t -> unit

(** [append x y] inserts all elements of [y] to the end of [x], mutating
    [x] inplace. *)
val append : 'a t -> 'a t -> unit

(** [unsafe_get t i] returns the element at index [i] from [t].

    If [i] is out of bounds, then the result is undefined.
*)
val unsafe_get : 'a t -> int -> 'a

(** [unsafe_set t i x] sets the element at index [i] to [x] in [t].

    If [i] is out of bounds, then the result is undefined.
*)
val unsafe_set : 'a t -> int -> 'a -> unit

(** [push t x] appends [x] to the end of [t]. *)
val push : 'a t -> 'a -> unit

(** [pop_exn t] removes and returns the element at the end of [t].

    @raise Invalid_argument if [t] is empty.
*)
val pop_exn : 'a t -> 'a

(** Same as [pop_exn], but returns [None] if the array is empty. *)
val pop : 'a t -> 'a option

(** [get_exn t i] returns the element at index [i] from [t].

    @raise Invalid_argument if [i] is out of bounds.
*)
val get_exn : 'a t -> int -> 'a

(** Same as [get], but returns [None] if [i] is out of bounds. *)
val get : 'a t -> int -> 'a option

(** Same as [get_exn t 0]. *)
val front_exn : 'a t -> 'a

(** Same as [get t 0]. *)
val front : 'a t -> 'a option

(** Same as [get_exn t (length t - 1)]. *)
val back_exn : 'a t -> 'a

(** Same as [get t (length t - 1)]. *)
val back : 'a t -> 'a option

(** [set_exn t i x] sets the element at index [i] to [x] in [t].

    @raise Invalid_argument if [i] is out of bounds.
*)
val set_exn : 'a t -> int -> 'a -> unit

(** Same as [set_exn], but returns an [Error _] if [i] is out of bounds. *)
val set : 'a t -> int -> 'a -> unit Or_error.t

(** [fold_until t ~init ~f ~finish] is a short-circuiting version of [fold].

    If [f] returns [Stop _] the computation ceases and results in that value.

    If [f] returns [Continue _], the fold will proceed.

    If [f] never returns [Stop _], [finish] is called on the accumulated
    value after the last iteration of [f].
*)
val fold_until :
  'a t ->
  init:'b ->
  f:('b -> 'a -> ('b, 'c) Continue_or_stop.t) ->
  finish:('b -> 'c) ->
  'c

(** Accumulates a value over each element, providing the index of each
    element. *)
val foldi : 'a t -> init:'b -> f:(int -> 'b -> 'a -> 'b) -> 'b

(** Accumulates a value over each element. *)
val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b

(** Same as [fold], but starts from the end of the array. *)
val fold_right : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b

(** Applies [f] for each element and its index. *)
val iteri : 'a t -> f:(int -> 'a -> unit) -> unit

(** Applies [f] for each element. *)
val iter : 'a t -> f:('a -> unit) -> unit

(** Same as [iteri], but starts from the end of the array. *)
val iteri_rev : 'a t -> f:(int -> 'a -> unit) -> unit

(** Same as [iter], but starts from the end of the array. *)
val iter_rev : 'a t -> f:('a -> unit) -> unit

(** Returns the first element, starting from index 0, that satisfies [f].

    The index of each element is provided to [f].
*)
val findi : 'a t -> f:(int -> 'a -> bool) -> 'a option

(** Returns the first element, starting from index 0, that satisfies [f]. *)
val find : 'a t -> f:('a -> bool) -> 'a option

(** Returns the first element, starting from index 0, where [f] returns
    [Some _].

    The index of each element is provided to [f].
*)
val find_mapi : 'a t -> f:(int -> 'a -> 'b option) -> 'b option

(** Returns the first element, starting from index 0, where [f] returns
    [Some _]. *)
val find_map : 'a t -> f:('a -> 'b option) -> 'b option

(** Transforms each element of the array according to [f].

    The index of each element is provided to [f].
*)
val mapi_inplace : 'a t -> f:(int -> 'a -> 'a) -> unit

(** Transforms each element of the array according to [f]. *)
val map_inplace : 'a t -> f:('a -> 'a) -> unit

(** Returns a new array with each element transformed according to [f].

    The index of each element is provided to [f].
*)
val mapi : 'a t -> f:(int -> 'a -> 'b) -> 'b t

(** Returns a new array with each element transformed according to [f]. *)
val map : 'a t -> f:('a -> 'b) -> 'b t

(** Returns a new array with every element that satisfies [f].

    The index of each element is provided to [f].
*)
val filteri : 'a t -> f:(int -> 'a -> bool) -> 'a t

(** Returns a new array with every element that satisfies [f]. *)
val filter : 'a t -> f:('a -> bool) -> 'a t

(** Returns a new array with every element [x] where [f] returns [Some x].

    The index of each element is provided to [f].
*)
val filter_mapi : 'a t -> f:(int -> 'a -> 'b option) -> 'b t

(** Returns a new array with every element [x] where [f] returns [Some x]. *)
val filter_map : 'a t -> f:('a -> 'b option) -> 'b t

(** Same as [filteri], but mutates the array inplace. *)
val filteri_inplace : 'a t -> f:(int -> 'a -> bool) -> unit

(** Same as [filter], but mutates the array inplace. *)
val filter_inplace : 'a t -> f:('a -> bool) -> unit

(** Returns [true] if there exists an element that satisfies [f]. Note that
    if the array is empty, then the result is [false]. *)
val exists : 'a t -> f:('a -> bool) -> bool

(** Returns [true] if all elements in the array satisfy [f]. Note that if
    the array is empty, then the result is [true]. *)
val for_all : 'a t -> f:('a -> bool) -> bool

(** Removes all duplicate elements in the array that are adjacent to each
    other, according to [compare].

    It is useful to call [sort] with the [compare] predicate on the array
    before calling this function, in order to remove every duplicate element.
*)
val remove_consecutive_duplicates : 'a t -> compare:('a -> 'a -> int) -> unit

(** Returns a fixed-size array of every element. *)
val to_array : 'a t -> 'a array

(** Returns a list of every element. *)
val to_list : 'a t -> 'a list

(** Returns a list of every element, in reverse order. *)
val to_list_rev : 'a t -> 'a list

(** Returns a lazy sequence of every element in the array.

    Any modifications to the array are shared with the resulting sequence.
*)
val to_sequence_mutable : 'a t -> 'a seq

(** Returns a lazy sequence of every element in the array, in reverse order.

    Any modifications to the array are shared with the resulting sequence.
*)
val to_sequence_rev_mutable : 'a t -> 'a seq

(** Returns a lazy sequence of every element in the array. *)
val to_sequence : 'a t -> 'a seq

(** Returns a lazy sequence of every element in the array, in reverse order. *)
val to_sequence_rev : 'a t -> 'a seq

(** Converts a fixed-size array into the dynamic array. *)
val of_array : 'a array -> 'a t

(** Converts a list into the dynamic array. *)
val of_list : 'a list -> 'a t

(** Sorts the array from [pos] to [pos + len - 1] according to [compare]. *)
val sort : ?pos:int -> ?len:int -> 'a t -> compare:('a -> 'a -> int) -> unit

(** Equivalent to

    {[
      sort t ~compare;
      remove_consecutive_duplicates t ~compare
    ]}
*)
val dedup_and_sort : 'a t -> compare:('a -> 'a -> int) -> unit
