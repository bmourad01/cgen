(** A specialized set for bit-indexed elements. *)

open Regular.Std

(** The key for indexing into the set. *)
type key = int

(** The bitset. *)
type t = private Z.t [@@deriving compare, equal, sexp]

(** The empty set. *)
val empty : t

(** Returns [true] if the set is empty. *)
val is_empty : t -> bool

(** Returns the singleton set of a key. *)
val singleton : key -> t

(** Set union. *)
val union : t -> t -> t

(** Set intersection. *)
val inter : t -> t -> t

(** Add an element to the set. *)
val set : t -> key -> t

(** Remove an element from the set. *)
val clear : t -> key -> t

(** Returns [true] if the element is in the set. *)
val mem : t -> key -> bool

(** Constructs the set where the first [n] elements
    are set. *)
val init : int -> t

(** Returns the least element of the set.

    @raise Invalid_argument if the set is empty
*)
val min_elt_exn : t -> key

(** Same as [min_elt_exn], but returns [None] if
    the set is empty. *)
val min_elt : t -> key option

(** Returns the greatest element of the set.

    @raise Invalid_argument if the set is empty
*)
val max_elt_exn : t -> key

(** Same as [max_elt_exn], but returns [None] if
    the set is empty. *)
val max_elt : t -> key option

(** Pops the least element of the set, returning the
    element and the updated set.

    @raise Invalid_argument if the set is empty
*)
val pop_min_elt_exn : t -> key * t

(** Same as [pop_min_elt_exn], but returns [None] if
    the set is empty. *)
val pop_min_elt : t -> (key * t) option

(** Pops the greatest element of the set, returning the
    element and the updated set.

    @raise Invalid_argument if the set is empty
*)
val pop_max_elt_exn : t -> key * t

(** Same as [pop_max_elt_exn], but returns [None] if
    the set is empty. *)
val pop_max_elt : t -> (key * t) option

(** Produces the sequence of elements in the set,
    according to [rev].

    If [rev] is [true], then the order is descending,
    otherwise, the order is ascending. The default is
    [false].
*)
val enum : ?rev:bool -> t -> key seq
