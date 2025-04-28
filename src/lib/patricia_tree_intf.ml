(** The interface for PATRICIA trees.

    This is an efficient specialization of a radix trie, which has a
    performance advantage over the standard library implementation of
    a binary tree for integral types.
*)

open Regular.Std

(** The interface required for keys of the tree, which are expected
    to be an integral/bitvector type. *)
module type Key = sig
  type t [@@deriving compare, equal]

  (** Zero value. *)
  val zero : t

  (** One value. *)
  val one : t

  (** The maximum bit capacity of [t]. *)
  val size : int

  (** Conversion to OCaml [int]. *)
  val to_int : t -> int

  (** Conversion from OCaml [int]. *)
  val of_int : int -> t

  (** Subtraction. *)
  val (-) : t -> t -> t

  (** Logical shift left. *)
  val (lsl) : t -> int -> t

  (** Logical shfit right. *)
  val (lsr) : t -> int -> t

  (** Logical AND. *)
  val (land) : t -> t -> t

  (** Logical OR. *)
  val (lor) : t -> t -> t

  (** Logical XOR. *)
  val (lxor) : t -> t -> t

  (** Logical NOT. *)
  val lnot : t -> t

  (** Count leading zeros. *)
  val clz : t -> int

  (** Pretty-printing. *)
  val pp : Format.formatter -> t -> unit
end

(** The signature for trees. *)
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

  (** Adds the key-value pair to the tree. If [key] is already
      present, then [data] is appended to the existing list
      associated with [key]. *)
  val add_multi : 'a list t -> key:key -> data:'a -> 'a list t

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

  (** Accumulates a result for each key-value pair in the tree, in
      increasing order. *)
  val fold : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** Accumulates a result for each key-value pair in the tree, in
      decreasing order. *)
  val fold_right : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** Returns the number of elements in the tree. *)
  val length : 'a t -> int

  (** Returns a list of all keys in the tree, in increasing order. *)
  val keys : 'a t -> key list

  (** Returns a list of all values in the tree, in inrcreasing order
      with respect to their corresponding keys.  *)
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

  (** Given an equality predicate for elements of the tree, returns
      [true] if both trees are equal. *)
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

  (** Given an ordering predicate for elements of the tree, returns
      an ordering for the two trees. *)
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
end

(** The signature for sets. *)
module type Set = sig
  (** The key into the set. *)
  type key

  (** The set. *)
  type t

  val empty : t

  (** Returns [true] if the tree is empty. *)
  val is_empty : t -> bool

  (** Returns [true] if the key is present. *)
  val mem : t -> key -> bool

  (** [singleton k] returns a singleton set for [k]. *)
  val singleton : key -> t

  (** Adds the key to the set if the key is not present. *)
  val add : t -> key -> t

  (** Removes the key from the set. *)
  val remove : t -> key -> t

  (** Combines two sets together. *)
  val union : t -> t -> t

  (** Intersects two sets (i.e. returns the set that has elements of both). *)
  val inter : t -> t -> t

  (** Returns [true] if the two sets are equal. *)
  val equal : t -> t -> bool

  (** Compares the two sets and returns an ordering. *)
  val compare : t -> t -> int

  (** Iterates the set according to [f]. *)
  val iter : t -> f:(key -> unit) -> unit

  (** Accumulates a result for each key in the set, in increasing order. *)
  val fold : t -> init:'a -> f:('a -> key -> 'a) -> 'a

  (** Accumulates a result for each key in the set, in decreasing order. *)
  val fold_right : t -> init:'a -> f:(key -> 'a -> 'a) -> 'a

  (** Transforms the set according to [f]. *)
  val map : t -> f:(key -> key) -> t

  (** Returns the number of elements in the set. *)
  val length : t -> int

  (** Returns a list of all keys in the set, in increasing order. *)
  val to_list : t -> key list

  (** Constructs a set from a list of keys. *)
  val of_list : key list -> t

  (** Returns a sequence of each key in the set according to [order]. By
      default, it is [`Increasing_key]. *)
  val to_sequence : ?order:[`Increasing | `Decreasing] -> t -> key seq

  (** Returns a set from a sequence. *)
  val of_sequence : key seq -> t
end
