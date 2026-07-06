open Base

(** A name for a key. *)
module type Name = sig
  type t
  val to_string : t -> string
end

(** A dictionary key. *)
module type Key = sig
  type uid
  type name

  (** A key that stores a value of type ['a]. *)
  type 'a t

  val compare : 'a t -> 'b t -> int
  val equal : 'a t -> 'b t -> bool

  (** [create ~name show] creates a fresh key with name [name] and a [show]
      function used for introspection. *)
  val create : name:name -> ('a -> Sexp.t) -> 'a t

  (** The unique identifier of the key. *)
  val uid : 'a t -> uid

  (** The declared name of the key. *)
  val name : 'a t -> name

  (** Serialize a value using the key's stored [show] function. *)
  val to_sexp : 'a t -> 'a -> Sexp.t

  (** Prove that two equal keys index the same type.

      Raises [Failure] if the keys are not equal.
  *)
  val same : 'a t -> 'b t -> ('a, 'b) Type_equal.t
end

(** A heterogeneous, type-safe dictionary. *)
module type S = sig
  exception Not_found
  exception Duplicate

  type 'a key
  type t [@@deriving sexp_of]

  (** A polymorphic visitor accumulating a value of type ['r]. *)
  type 'r visitor = {
    visit : 'a. 'a key -> 'a -> 'r -> 'r;
  }

  (** A polymorphic merge: called on keys present in both dicts. *)
  type merge = {
    merge : 'a. 'a key -> 'a -> 'a -> 'a;
  }

  val pp : Stdlib.Format.formatter -> t -> unit
  val pp_key : Stdlib.Format.formatter -> 'a key -> unit

  (** The empty dict. *)
  val empty : t

  (** Returns [true] if the dict is empty. *)
  val is_empty : t -> bool

  (** The number of bindings. *)
  val length : t -> int

  (** Constructs a singleton dict. *)
  val singleton : 'a key -> 'a -> t

  (** Returns [true] if the key is bound. *)
  val mem : 'a key -> t -> bool

  (** [set k v t] binds [k] to [v], overwriting any previous binding. *)
  val set : 'a key -> 'a -> t -> t

  (** [add k v t] binds [k] to [v], returning [`Duplicate] if already bound. *)
  val add : 'a key -> 'a -> t -> [`Ok of t | `Duplicate]

  (** [update f k v t] binds [k] to [v], or to [f old v] on collision (where
      [old] is the existing value). *)
  val update : ('a -> 'a -> 'a) -> 'a key -> 'a -> t -> t

  (** [get k t] returns the value bound to [k].

      Raises [Not_found] if [k] is not bound.
  *)
  val get : 'a key -> t -> 'a

  (** Like [get], but returns [None] if [k] is not bound. *)
  val find : 'a key -> t -> 'a option

  (** [remove k t] removes the binding for [k]. *)
  val remove : 'a key -> t -> t

  (** [change k t ~f] updates the binding for [k] according to [f]. *)
  val change : 'a key -> t -> f:('a option -> 'a option) -> t

  (** [merge m x y] unions [x] and [y], calling [m.merge k xv yv] for keys
      present in both (the value from [x] passed first). *)
  val merge : merge -> t -> t -> t

  (** Fold the visitor over all bindings, in ascending key order. *)
  val foreach : t -> init:'r -> 'r visitor -> 'r

  (** Internal methods, explicitly undocumented. *)
  module Internal : sig
    val is_rank1 : t -> bool
    val insert : 'a key -> 'a -> t -> t
  end
end
