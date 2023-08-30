(** A heterogeneous dictionary.

    The implementation and interface is adapted from the one used
    in Binary Analysis Platform (BAP).
*)

open Regular.Std

(** The interface required to lift a type to [value]. *)
module type S = sig
  type t [@@deriving bin_io, compare, sexp]
  val pp : Format.formatter -> t -> unit
end

(** Persistent type identifier. *)
type typeid [@@deriving bin_io, compare, equal, sexp]

(** A universal value. *)
type value [@@deriving compare, equal, sexp]

val pp_value : Format.formatter -> value -> unit

(** A tag constructor of type ['a]. *)
type 'a tag

(** [register ~uuid name (module T)] creates a new variant constructor
    that accepts values of type [T.t].

    The returned value of type [T.t tag] is a special key that can be used
    with [create] and [get] functions to pack and unpack values of type
    [T.t] into [value].
*)
val register : uuid:string -> string -> (module S with type t = 'a) -> 'a tag

(** [create t x] creates a value [x] with tag [t]. *)
val create: 'a tag -> 'a -> value

(** [is t v] returns [true] if [v] was constructed with the tag [t]. *)
val is : 'a tag -> value -> bool

(** Returns the name of a value's tag. *)
val tagname : value -> string

(** Returns the type identifier of a value. *)
val typeid : value -> string

(** [get v t] attempts to extract the value associated with
    [t] in [v]. *)
val get : 'a tag -> value -> 'a option

(** Same as [get], but raises if the value doesn't exist. *)
val get_exn : 'a tag -> value -> 'a

(** The dictionary. *)
type t [@@deriving bin_io, compare, equal, sexp]

(** The empty dictionary. *)
val empty : t

(** Returns [true] if the dictionary is empty. *)
val is_empty : t -> bool

(** [set d t v] sets the tag [t] to value [v] in [d], overwriting
    the previous value if it exists. *)
val set : t -> 'a tag -> 'a -> t

(** [remove d t] removes the binding for tag [t] in [d]. *)
val remove : t -> 'a tag -> t

(** [mem d t] returns true if [t] has a binding in [d]. *)
val mem : t -> 'a tag -> bool

(** [find d t] returns the binding for [t] in [d], if it exists. *)
val find : t -> 'a tag -> 'a option

(** [find_exn d t] returns the binding for [t] in [d]. Raises if
    it doesn't exist. *)
val find_exn : t -> 'a tag -> 'a

(** [add d t v] attemts to add a binding from [t] to [v] in [d],
    returning [`Duplicate] if a binding already exists. *)
val add : t -> 'a tag -> 'a -> [`Duplicate | `Ok of t]

(** [change d t ~f] changes the binding for [t] in [d] according
    to [f]. *)
val change : t -> 'a tag -> f:('a option -> 'a option) -> t

(** Returns the sequence of all [value] entries. *)
val data : t -> value seq

(** Returns the sequence of all [typeid]-[value] entries. *)
val to_sequence : t -> (typeid * value) seq

(** [filter t ~f] retains values [v] in [t] where [f v] returns [true]. *)
val filter : t -> f:(value -> bool) -> t
