module type Key = sig
  type t [@@deriving compare, equal, sexp]
end

(** Interface for a small map. *)
module type S = sig
  type key [@@deriving compare, equal, sexp]
  type 'a t [@@deriving compare, equal, sexp]

  exception Not_found
  exception Duplicate

  (** The empty map. *)
  val empty : 'a t

  (** Returns [true] if the map is empty. *)
  val is_empty : 'a t -> bool

  (** Transform each value of the map according to [f]. *)
  val map : 'a t -> f:('a -> 'b) -> 'b t

  (** Applies [f] to each value of the map. *)
  val iter : 'a t -> f:('a -> unit) -> unit

  (** Applies [f] to each key-and-value of the map. *)
  val iteri : 'a t -> f:(key:key -> data:'a -> unit) -> unit

  (** Fold over the values of the map, in ascending order according
      to [Key.compare]. *)
  val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b

  (** Fold over the values of the map, in descending order according
      to [Key.compare]. *)
  val fold_right : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b

  (** Fold over the key-value pairs of the map, in ascending order
      according to [Key.compare]. *)
  val foldi : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** Fold over the key-value pairs of the map, in descending order
      according to [Key.compare]. *)
  val foldi_right : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** [set t ~key ~data] associates [key] with [data], in the map [t],
      replacing the previous value if [key] was already present. *)
  val set : 'a t -> key:key -> data:'a -> 'a t

  (** [remove t k] removes any assocations for key [k] in [t]. *)
  val remove : 'a t -> key -> 'a t

  (** [update t k ~f] updates the value associated with [k] in [t] according
      to [f]. *)
  val update : 'a t -> key -> f:('a option -> 'a) -> 'a t

  (** Similar to [update], but accepts two functions [has] and [nil] for
      the cases where the key is or is not present, respectively. *)
  val update_with : 'a t -> key -> has:('a -> 'a) -> nil:(unit -> 'a) -> 'a t

  (** Merges two maps according to [f].

      Upon collision, [f ~key v1 v2] is called, where [v1] is from the left
      map, and [v2] is from the right map. *)
  val merge : 'a t -> 'a t -> f:(key:key -> 'a -> 'a -> 'a) -> 'a t

  (** Like [set], but returns [`Duplicate] if the [key] is already present,
      and [`Ok t] otherwise, where [t] is the updated map. *)
  val add : 'a t -> key:key -> data:'a -> [`Ok of 'a t | `Duplicate]

  (** Exceptional version of [add].

      Raises [Duplicate] if [key] is already present *)
  val add_exn : 'a t -> key:key -> data:'a -> 'a t

  (** [find t k] returns [Some v] if [k] is present in [t], and [None] otherwise. *)
  val find : 'a t -> key -> 'a option

  (** Exceptional version of [find].

      Raises [Not_found] if [key] is not present
  *)
  val find_exn : 'a t -> key -> 'a

  (** Returns [true] if the key is present in the map. *)
  val mem : 'a t -> key -> bool

  (** Returns the number of elements present in the map. *)
  val length : 'a t -> int

  (** Returns, in ascending order, a list of all key-value pairs. *)
  val to_list : 'a t -> (key * 'a) list

  (** Returns, in descending order, a list of all key-value pairs. *)
  val to_list_rev : 'a t -> (key * 'a) list

  (** Returns a list of all keys. *)
  val keys : 'a t -> key list

  (** Returns a list of all values. *)
  val data : 'a t -> 'a list

  (** Constructs a singleton map. *)
  val singleton : key -> 'a -> 'a t

  (** Constructs a map from an association list.

      Raises [Duplicate] on a duplicate key in the list
  *)
  val of_alist_exn : (key * 'a) list -> 'a t

  (** Non-exceptional version of [of_alist_exn]. *)
  val of_alist : (key * 'a) list -> [`Ok of 'a t | `Duplicate]

  (** Returns, in ascending order, a sequence of all key-value pairs. *)
  val to_sequence : 'a t -> (key * 'a) Base.Sequence.t

  (** Returns, in descending order, a sequence of all key-value pairs. *)
  val to_sequence_rev : 'a t -> (key * 'a) Base.Sequence.t

  (** Compares two maps using a total ordering. *)
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

  (** Returns [true] if both maps are equal. *)
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end
