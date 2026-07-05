(** A specialized set for bit-indexed elements. *)


(** The key for indexing into the set. *)
type key = int

(** The bitset. *)
type t [@@deriving compare, equal, sexp]

(** [create ?capacity ()] is a fresh empty set. *)
val create : ?capacity:int -> unit -> t

(** Returns a copy of the set. *)
val copy : t -> t

(** Returns the number of elements in the set. *)
val cardinality : t -> int

(** The singleton set containing [key]. *)
val singleton : key -> t

(** Returns [true] if the set is empty. *)
val is_empty : t -> bool

(** Returns [true] if the element is in the set. *)
val mem : t -> key -> bool

(** Adds an element to the set. *)
val add : t -> key -> unit

(** Removes an element from the set. *)
val remove : t -> key -> unit

(** Removes all elements from the set. *)
val clear : t -> unit

(** Constructs the set where the first [n] elements are present. *)
val init : int -> t

(** [union a b] adds every element of [b] to [a]. *)
val union : t -> t -> unit

(** [inter a b] keeps only the elements of [a] that are also in [b]. *)
val inter : t -> t -> unit

(** [diff a b] removes every element of [b] from [a]. *)
val diff : t -> t -> unit

(** Returns the least element of the set, or [None] if empty. *)
val min_elt : t -> key option

(** Returns the least element of the set.

    Raises [Invalid_argument] if the set is empty.
*)
val min_elt_exn : t -> key

(** Returns the greatest element of the set, or [None] if empty. *)
val max_elt : t -> key option

(** Returns the greatest element of the set.

    Raises [Invalid_argument] if the set is empty.
*)
val max_elt_exn : t -> key

(** Removes and returns the least element of the set.

    Raises [Invalid_argument] if the set is empty.
*)
val pop_min_exn : t -> key

(** Removes and returns the greatest element of the set.

    Raises [Invalid_argument] if the set is empty.
*)
val pop_max_exn : t -> key

(** Produces the sequence of elements in the set, according to [rev].

    If [rev] is [true], then the order is descending, otherwise the order is
    ascending. The default is [false].
*)
val enum : ?rev:bool -> t -> key Base.Sequence.t

(** [fold ?rev t ~init ~f] folds over elements in ascending (or descending if
    [rev]) order. *)
val fold : ?rev:bool -> t -> init:'a -> f:('a -> key -> 'a) -> 'a

(** [iter ?rev t ~f] iterates over elements in ascending (or descending if
    [rev]) order. *)
val iter : ?rev:bool -> t -> f:(key -> unit) -> unit

(** [for_all t ~f] returns [true] iff [f] holds for every element. *)
val for_all : t -> f:(key -> bool) -> bool
