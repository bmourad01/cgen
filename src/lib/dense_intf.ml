(** Open-addressing hash tables and sets for integer-like keys.

    Inspired by LLVM's [DenseMap]/[DenseSet]. Uses Robin Hood probing
    with shift-back deletion, so there are no tombstones.

    Requires the key type to reserve a sentinel value that is never a
    legitimate key ([empty_sentinel]).

    These structures are not thread-safe.
*)

(** The interface required for keys. *)
module type Key = sig
  type t [@@deriving equal] [@@immediate64]

  (** A value of [t] that will never appear as a legitimate key.

      Used as the "empty slot" marker in the underlying array.
  *)
  val empty_sentinel : t

  (** Conversion to [int] for hashing. *)
  val to_int : t -> int

  val pp : Format.formatter -> t -> unit
end

(** The signature for mutable, open-addressing hash maps. *)
module type Map = sig
  type key
  type 'a t

  (** Raised when a duplicate key is inserted. *)
  exception Duplicate

  (** Raised when a requested key is not present. *)
  exception Not_found

  (** [create ?capacity ()] creates a fresh table.

      [capacity] is a hint for the initial number of slots (rounded up
      to a power of 2).
  *)
  val create : ?capacity:int -> unit -> 'a t

  (** Removes all elements. *)
  val clear : 'a t -> unit

  (** Current number of elements. *)
  val length : 'a t -> int

  (** Equivalent to [length t = 0]. *)
  val is_empty : 'a t -> bool

  (** Returns [true] if the key is present in the table. *)
  val mem : 'a t -> key -> bool

  (** Looks up the value mapped to the key, if present. Otherwise
      returns [None]. *)
  val find : 'a t -> key -> 'a option

  (** Looks up the value mapped to the key, if present.

      @raise Not_found if the key is not present
  *)
  val find_exn : 'a t -> key -> 'a

  (** Inserts or updates the mapping from [key] to [data]. *)
  val set : 'a t -> key:key -> data:'a -> unit

  (** Inserts the mapping from [key] to [data].

      @raise Duplicate if [key] already exists.
  *)
  val add_exn : 'a t -> key:key -> data:'a -> unit

  (** Returns the existing mapping for [key], or inserts
      [default ()] and returns it. *)
  val find_or_add : 'a t -> key -> default:(unit -> 'a) -> 'a

  (** Replaces the data for [key] by [f (find t key)]. *)
  val update : 'a t -> key -> f:('a option -> 'a) -> unit

  (** Same as [update], but [f] can remove the entry. *)
  val change : 'a t -> key -> f:('a option -> 'a option) -> unit

  (** [add_multi t ~key ~data] prepends [data] to the list at [key],
      or starts a fresh list. *)
  val add_multi : 'a list t -> key:key -> data:'a -> unit

  (** Removes the entry for [key], if present. *)
  val remove : 'a t -> key -> unit

  (** Apply [f] to each value in the table. No order is guaranteed. *)
  val iter : 'a t -> f:('a -> unit) -> unit

  (** Apply [f] to each key in the table. No order is guaranteed. *)
  val iter_keys : 'a t -> f:(key -> unit) -> unit

  (** Apply [f] to each [key] and [data] mapping in the table. No order
      is guaranteed. *)
  val iteri : 'a t -> f:(key:key -> data:'a -> unit) -> unit

  (** Accumulate a value (starting with [init]) over each [key] and [data]
      mapping in the table. No order is guaranteed. *)
  val fold : 'a t -> init:'b -> f:(key:key -> data:'a -> 'b -> 'b) -> 'b

  (** Update each value in the table according to [f]. *)
  val map_inplace : 'a t -> f:('a -> 'a) -> unit

  (** Same as [map_inplace], but the [key] is provided along with the
      [data]. *)
  val mapi_inplace : 'a t -> f:(key:key -> data:'a -> 'a) -> unit

  (** Returns each key of the table as a list, in no particular order. *)
  val keys : 'a t -> key list

  (** Returns each value of the table as a list, in no particular order. *)
  val data : 'a t -> 'a list

  (** Returns each key-value pair of the table as a list, in no particular order. *)
  val to_alist : 'a t -> (key * 'a) list
end

(** The signature for mutable, open-addressing hash sets. *)
module type Set = sig
  type key
  type t

  (** [create ?capacity ()] creates a fresh set.

      [capacity] is a hint for the initial number of slots (rounded up
      to a power of 2).
  *)
  val create : ?capacity:int -> unit -> t

  (** Removes all elements. *)
  val clear : t -> unit

  (** Current number of elements. *)
  val length : t -> int

  (** Equivalent to [length t = 0]. *)
  val is_empty : t -> bool

  (** Returns [true] if the key is an element of the set. *)
  val mem : t -> key -> bool

  (** Adds the key to the set. No-op if already present. *)
  val add : t -> key -> unit

  (** Adds the key to the set. Returns [false] if already present. *)
  val strict_add : t -> key -> bool

  (** Removes the key from the set. No-op if absent. *)
  val remove : t -> key -> unit

  (** Apply [f] to each key in the set, in no particular order. *)
  val iter : t -> f:(key -> unit) -> unit

  (** Accumulate a value (starting with [init]) over each element of
      the set, in no particular order. *)
  val fold : t -> init:'a -> f:('a -> key -> 'a) -> 'a

  (** Returns each key of the set as a list, in no particular order. *)
  val to_list : t -> key list
end
