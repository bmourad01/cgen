(** An immutable hash map; for internal use only.

    Question: why use this over a [Hashtbl]?

    Answer: this data structure is persistent and immutable,
    so passes and analyses that are sensitive to scoping (e.g.
    dominator tree traversals), can share results more efficiently.

    Question: why use this over a [Map]?

    Answer: if your key type is expensive to compare, but cheaper
    to hash, then this data structure may end up having better
    performance characteristics overall.
*)

open Regular.Std

module type S = sig
  (** The key into the map. *)
  type key

  (** The map. *)
  type +'a t

  (** Returned when calling [add], and indicates whether a key
      already exists in the map. *)
  type 'a or_duplicate = [
    | `Ok of 'a t
    | `Duplicate
  ]

  (** Raised by [add_exn] when a duplicate key is provided. *)
  exception Duplicate

  (** Raised by [find_exn] when a key is not present. *)
  exception Not_found

  (** The empty map. *)
  val empty : 'a t

  (** Returns [true] if the map is empty. *)
  val is_empty : 'a t -> bool

  (** Attempts to find the data associated with a key.

      @raise Not_found if the key is not present.
  *)
  val find_exn : 'a t -> key -> 'a

  (** Attempts to find the data associated with a key. *)
  val find : 'a t -> key -> 'a option

  (** Returns [true] if the key is present. *)
  val mem : 'a t -> key -> bool

  (** [singleton k v] returns a single mapping from [k] to [v]. *)
  val singleton : key -> 'a -> 'a t

  (** Adds the key-value pair to the map, replacing the existing
      entry if it is present. *)
  val set : 'a t -> key:key -> data:'a -> 'a t

  (** Adds the key-value pair to the map. If [key] is already
      present, then [data] is appended to the existing list
      associated with [key]. *)
  val add_multi : 'a list t -> key:key -> data:'a -> 'a list t

  (** Adds the key-value pair to the map.

      @raise Duplicate if the key is already present.
  *)
  val add_exn : 'a t -> key:key -> data:'a -> 'a t

  (** Adds the key-value pair to the map if the key is not
      present. *)
  val add : 'a t -> key:key -> data:'a -> 'a or_duplicate

  (** Removes the key and its associated data from the map. *)
  val remove : 'a t -> key -> 'a t

  (** Updates the data associated with the key according to [f]. *)
  val update : 'a t -> key -> f:('a option -> 'a) -> 'a t

  (** Similar to [update]. If the key is present, then [has] is called
      with the existing data, otherwise [nil] is called. *)
  val update_with : 'a t -> key -> has:('a -> 'a) -> nil:(unit -> 'a) -> 'a t

  (** Same as [update], but [f] can remove the element from the map. *)
  val change : 'a t -> key -> f:('a option -> 'a option) -> 'a t

  (** Combines two maps together according to [f]. *)
  val merge : 'a t -> 'a t -> f:(key:key -> 'a -> 'a -> 'a) -> 'a t

  (** Iterates the map according to [f]. *)
  val iter : 'a t -> f:(key:key -> data:'a -> unit) -> unit

  (** Accumulates a result for each key-value pair in the map. *)
  val fold : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** Returns the number of elements in the map. *)
  val length : 'a t -> int

  (** Returns a list of all keys in the map. No particular order is guaranteed. *)
  val keys : 'a t -> key list

  (** Returns a list of all values in the map. No particular order is guaranteed *)
  val data : 'a t -> 'a list

  (** Creates a map from an association list.

      @raise Duplicate if the list has duplicate keys.
  *)
  val of_alist_exn : (key * 'a) list -> 'a t

  (** Same as [of_alist_exn], but returns [None] instead of raising
      when duplicate keys are present. *)
  val of_alist : (key * 'a) list -> 'a t option

  (** Returns a list of each key-value pair in the map. *)
  val to_list : 'a t -> (key * 'a) list

  (** Returns a sequence of each key-value pair in the map. *)
  val to_sequence : 'a t -> (key * 'a) seq  
end
