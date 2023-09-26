(** The interface for PATRICIA trees. *)

open Regular.Std

(** The interface required for keys of the tree. *)
module type Key = sig
  type t [@@deriving compare, equal]

  val zero : t
  val one : t
  val size : int
  val to_int : t -> int
  val of_int : int -> t
  val (-) : t -> t -> t
  val (lsl) : t -> int -> t
  val (lsr) : t -> int -> t
  val (land) : t -> t -> t
  val (lor) : t -> t -> t
  val (lxor) : t -> t -> t
  val lnot : t -> t
  val clz : t -> int
  val pp : Format.formatter -> t -> unit
end

module type S = sig
  (** The key into the tree. *)
  type key

  (** The tree. *)
  type +'a t

  (** Returned when calling [add], and indicates whether a key
      already exists in the tree. *)
  type 'a or_duplicate = [
    | `Ok of 'a t
    | `Duplicate
  ]

  (** Raised by [add_exn] when a duplicate key is provided. *)
  exception Duplicate

  (** Raised by [find_exn] when a key is not present. *)
  exception Not_found

  (** The empty tree. *)
  val empty : 'a t

  (** Returns [true] if the tree is empty. *)
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

  (** Adds the key-value pair to the tree, replacing the existing
      entry if it is present. *)
  val set : 'a t -> key:key -> data:'a -> 'a t

  (** Adds the key-value pair to the tree.

      @raise Duplicate if the key is already present.
  *)
  val add_exn : 'a t -> key:key -> data:'a -> 'a t

  (** Adds the key-value pair to the tree if the key is not
      present. *)
  val add : 'a t -> key:key -> data:'a -> 'a or_duplicate

  (** Removes the key and its associated data from the tree. *)
  val remove : 'a t -> key -> 'a t

  (** Updates the data associated with the key according to [f]. *)
  val update : 'a t -> key -> f:('a option -> 'a) -> 'a t

  (** Similar to [update]. If the key is present, then [has] is called
      with the existing data, otherwise [nil] is called. *)
  val update_with : 'a t -> key -> has:('a -> 'a) -> nil:(unit -> 'a) -> 'a t

  (** Same as [update], but [f] can remove the element from the tree. *)
  val change : 'a t -> key -> f:('a option -> 'a option) -> 'a t

  (** Combines two trees together according to [f]. *)
  val merge : 'a t -> 'a t -> f:(key:key -> 'a -> 'a -> 'a) -> 'a t

  (** Iterates the tree according to [f]. *)
  val iter : 'a t -> f:(key:key -> data:'a -> unit) -> unit

  (** Accumulates a result for each key-value pair in the tree. *)
  val fold : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** Returns the number of elements in the tree. *)
  val length : 'a t -> int

  (** Returns a list of all keys in the tree. *)
  val keys : 'a t -> key list

  (** Returns a list of all values in the tree. *)
  val data : 'a t -> 'a list

  (** Creates a tree from an association list.

      @raise Duplicate if the list has duplicate keys.
  *)
  val of_alist_exn : (key * 'a) list -> 'a t

  (** Same as [of_alist_exn], but returns [None] instead of raising
      when duplicate keys are present. *)
  val of_alist : (key * 'a) list -> 'a t option

  (** Returns a list of each key-value pair in the tree in increasing
      order. *)
  val to_list : 'a t -> (key * 'a) list

  (** Returns a sequence of each key-value pair in the tree according
      to [order]. By default, it is [`Increasing_key]. *)
  val to_sequence :
    ?order:[`Increasing_key | `Decreasing_key] ->
    'a t ->
    (key * 'a) seq  
end
