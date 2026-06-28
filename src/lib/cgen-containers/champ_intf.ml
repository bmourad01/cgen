module type S = sig
  type key

  (** A tree keyed by [key], with associated values of type ['a]. *)
  type 'a t

  exception Not_found
  exception Duplicate

  (** The empty tree. *)
  val empty : 'a t

  (** [find t k] looks up the value associated with [k] in [t], if it exists. *)
  val find : 'a t -> key -> 'a option

  (** Exceptional version of [find].

      @raise Not_found if the key is not present
  *)
  val find_exn : 'a t -> key -> 'a

  (** [mem t k] returns [true] if [k] is present in [t], [false] otherwise. *)
  val mem : 'a t -> key -> bool

  (** [set t ~key ~data] associates [key] with [data] in [t], replacing the
      previous value if [k] already exists. *)
  val set : 'a t -> key:key -> data:'a -> 'a t

  (** Like [set], but returns [`Ok t'] with the new tree if [k] was not
      already present, and [`Duplicate] otherwise. *)
  val add : 'a t -> key:key -> data:'a -> [`Ok of 'a t | `Duplicate]

  (** Exceptional version of [add].

      @raise Duplicate if the key is already present
  *)
  val add_exn : 'a t -> key:key -> data:'a -> 'a t

  (** [remove t k] removes [k] from [t]. If [k] was not present, the tree
      is unchanged. *)
  val remove : 'a t -> key -> 'a t

  (** [update t k] updates [k] in [t] according to [f].

      If [k] is not present, then [f None] is called, returning a new value
      to associate with [k].

      If [k] is present, then [f (Some v)] is called, where [v] is the current
      value associated with [k].
  *)
  val update : 'a t -> key -> f:('a option -> 'a) -> 'a t

  (** Like [update], but more general.

      [has v] is called when [k] is associated with a value [v].
      [nil ()] is called with [k] is not present in the tree.
  *)
  val update_with : 'a t -> key -> has:('a -> 'a) -> nil:(unit -> 'a) -> 'a t

  (** [iter t ~f] iterates over all values in [t] according to [f]. *)
  val iter : 'a t -> f:('a -> unit) -> unit

  (** [iteri t ~f] iterates over all key-value pairs in [t] according to [f]. *)
  val iteri : 'a t -> f:(key:key -> data:'a -> unit) -> unit

  (** [fold t ~init ~f] accumulates a value over [t] according to [f], with
      the initial value being [init]. *)
  val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b

  (** Like [fold], but [f] receives both the [key] and [data]. *)
  val foldi : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** Returns the tree as an association list. *)
  val to_alist : 'a t -> (key * 'a) list

  (** Returns a list of all keys in the tree. *)
  val keys : 'a t -> key list

  (** Returns a list of all values in the tree. *)
  val data : 'a t -> 'a list

  (** Returns the number of key-value pairs in the tree. *)
  val length : 'a t -> int

  (** Constructs a tree of a single key-value pair. *)
  val singleton : key -> 'a -> 'a t

  (** Constructs a tree from an association list.

      @raise Duplicate if the list has duplicate keys
  *)
  val of_alist_exn : (key * 'a) list -> 'a t

  (** Like [of_alist_exn], but returns [`Ok t] with the created tree
      if there are no duplicates, and [`Duplicate] otherwise. *)
  val of_alist : (key * 'a) list -> [`Ok of 'a t | `Duplicate]

  (** Constructs a key from an association list.

      If the list has duplicate keys, the right-most key-value pair
      is used, and the other duplicates are discarded.
  *)
  val of_alist_overwrite : (key * 'a) list -> 'a t
end
