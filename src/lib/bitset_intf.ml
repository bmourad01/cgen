open Regular.Std

module type Key = sig
  (** The key. *)
  type t

  val to_int : t -> int
  val of_int : int -> t
end

module type S = sig
  (** The key for indexing into the set. *)
  type key

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

  (** Produces the sequence of elements in the set,
      from lowest to highest. *)
  val enum : t -> key seq
end
