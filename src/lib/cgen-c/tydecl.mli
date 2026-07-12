(** Type declarations.

    These are the [struct], [union], [enum], and [typedef] definitions
    a declaration specifier introduces.
*)

(** A field in a [struct] or [union]. *)
type 'a field = {
  fname  : string;
  fty    : 'a Expr.ty;
  fbits  : 'a Expr.t option;
  (** Optional bit-width specifier. *)
  fattrs : 'a Attr.raws;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** An [enum] item. *)
type 'a eitem = {
  einame  : string;
  eivalue : 'a Expr.t option;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A type declaration node with its annotation. *)
type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Compound of {
      kind   : Type.compound;
      tag    : string;
      fields : 'a field list option;
      (** [None] for a forward declaration ([struct S;]), [Some fields] for
          a definition ([struct S { ... };], possibly with no fields). *)
      attrs  : 'a Attr.raws;
    } (** A [struct] or [union] declaration. *)
  | Enum of {
      tag   : string;
      items : 'a eitem list;
    } (** An [enum] definition. *)
  | Typedef of {
      name : string;
      ty   : 'a Expr.ty;
    } (** A type alias. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors} *)

val compound :
  ?attrs:'a Attr.raws ->
  kind:Type.compound ->
  tag:string ->
  fields:'a field list option ->
  ann:'a ->
  unit ->
  'a t

val enum : tag:string -> items:'a eitem list -> ann:'a -> 'a t
val typedef : name:string -> ty:'a Expr.ty -> ann:'a -> 'a t

val field :
  ?bits:'a Expr.t ->
  ?attrs:'a Attr.raws ->
  name:string ->
  ty:'a Expr.ty ->
  unit ->
  'a field

val eitem : ?value:'a Expr.t -> name:string -> unit -> 'a eitem

(** {1 Pretty printing} *)

val pp_field : Format.formatter -> 'a field -> unit
val pp : Format.formatter -> 'a t -> unit
val to_string : 'a t -> string
