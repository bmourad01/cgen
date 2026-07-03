(** Generic layout-computation functor.

    Computes memory layouts (size, alignment, per-field placement) for
    structs, unions, and opaque types.
*)

open Core

(** A computed layout with ['datum] as its members. *)
type 'datum layout [@@deriving bin_io, compare, equal, hash, sexp]

(** [sizeof l] is the size in bytes of [l]. *)
val sizeof : _ layout -> int

(** [align l] is the alignment requirement in bytes of [l]. *)
val align : _ layout -> int

(** Equivalent to [sizeof l = 0]. *)
val is_empty : _ layout -> bool

(** [members l] returns the members of the layout.

    [First] corresponds to a single compound type, while [Second]
    corresponds to a union of compound types.
*)
val members : 'datum layout -> ('datum list, 'datum list list) Either.t

(** A field representation, parameterized over the field type and the
    per-datum data stored in the resulting layout. *)
module type Field = sig
  (** A field of a compound type. *)
  type t [@@deriving bin_io, compare, equal, hash, sexp]

  (** One element of a layout's data sequence. *)
  type datum [@@deriving bin_io, compare, equal, hash, sexp]

  (** [pad n] constructs a padding datum spanning [n] bytes. *)
  val pad : int -> datum

  (** [opaque n] constructs an opaque-bytes datum spanning [n] bytes. *)
  val opaque : int -> datum

  (** [datum_bytes d] is the number of bytes occupied by [d]. *)
  val datum_bytes : datum -> int

  (** [try_merge a b] is [Some c] if two adjacent datums [a] and [b]
      can be combined into a single datum [c] (e.g. two consecutive
      pads), and [None] otherwise. *)
  val try_merge : datum -> datum -> datum option

  (** [refs f] returns the names of compound types referenced as value
      fields by [f].

      Note that pointer references do not count, since they do not force
      the referent's layout to be complete.
  *)
  val refs : t -> string list

  (** [field_data ~gamma ~enclosing f] returns the data sequence,
      alignment in bytes, and size in bytes for one field.

      [gamma] resolves named compound types to their layouts.

      [enclosing] is the name of the compound being laid out, used
      for self-reference detection.
  *)
  val field_data :
    gamma:(string -> datum layout) ->
    enclosing:string ->
    t ->
    datum list * int * int
end

(** Specializes the layout algorithm with the field representation
    supplied by [F]. *)
module Make(F : Field) : sig
  (** A computed layout. *)
  type t = F.datum layout [@@deriving bin_io, compare, equal, hash, sexp]

  (** A struct or union definition. *)
  type compound = [
    | `struct_ of string * int option * F.t list
    | `union   of string * int option * F.t list
  ]

  (** A named type definition: compound or opaque. *)
  type named = [
    | compound
    | `opaque of string * int * int
  ]

  (** [named_name t] is the name of the named type [t]. *)
  val named_name : named -> string

  (** [named_align t] is the explicit alignment of [t], if any. *)
  val named_align : named -> int option

  (** [create gamma t] computes the layout of named type [t].
      [gamma] resolves any named compound types referenced by [t].

      Raises [Invalid_argument] on malformed input (e.g. bad alignment,
      undeclared field types).
  *)
  val create : (string -> t) -> named -> t

  (** [of_types ts] computes layouts for all of [ts], performing
      topological ordering and cycle detection.

      Raises [Invalid_argument] on duplicate names, undeclared field
      types, or cycles among value-typed fields.
  *)
  val of_types : named list -> (string * t) list
end
