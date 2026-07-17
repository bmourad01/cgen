(** A heterogeneous dictionary of typed metadata.

    A thin facade over {!Cgen_containers.Hdict} that adds stable, [uuid]-named
    tags and [bin_io]/[compare]/[sexp] serialization (needed by the IR nodes
    that carry it).
*)

(** The interface required to lift a type to a tag's value. *)
module type S = sig
  type t [@@deriving bin_io, compare, sexp]
  val pp : Format.formatter -> t -> unit
end

(** A tag constructor for values of type ['a]. *)
type 'a tag

val pp_tag : Format.formatter -> 'a tag -> unit

(** [register name (module T)] creates a new tag that accepts values of type
    [T.t].

    Each call mints a fresh tag identity, so [name] serves only as the tag's
    stable serialization key. As a consequence, it must be unique across all
    registered tags, and stable across runs for serialized values to round-trip.

    Raises [Invalid_argument] when a duplicate [name] is passed.
*)
val register : string -> (module S with type t = 'a) -> 'a tag

(** The dictionary. *)
type t [@@deriving bin_io, compare, equal, sexp]

(** The empty dictionary. *)
val empty : t

(** [set d t v] binds tag [t] to value [v] in [d], overwriting any previous
    value. *)
val set : t -> 'a tag -> 'a -> t

(** Equivalent to [set empty t v]. *)
val singleton : 'a tag -> 'a -> t

(** [remove d t] removes the binding for tag [t] in [d]. *)
val remove : t -> 'a tag -> t

(** [mem d t] returns [true] if [t] has a binding in [d]. *)
val mem : t -> 'a tag -> bool

(** [find d t] returns the binding for [t] in [d], if any. *)
val find : t -> 'a tag -> 'a option
