(** The typing environment, used during typechecking and elaboration. *)

open Core

(** An enum element. *)
module Enum_element : sig
  type t [@@deriving bin_io, compare, equal, hash, sexp]

  (** The name of the enum element. *)
  val name : t -> string

  (** The tag (typename) associated with the element. *)
  val tag : t -> string

  (** The integer value of the enum element. *)
  val value : t -> int64
end

type enum_element = Enum_element.t [@@deriving bin_io, compare, equal, hash, sexp]

(** A tag type. *)
type tag =
  | Tenum of (string * int64) list
  (** An enum type consisting of elements paired with their
      corresponding values. *)
  | Tcompound of {
      kind   : Type.compound;
      fields : Tdecl.field list;
      attrs  : Attr.set;
      (** Attributes on the aggregate (e.g. [packed], [aligned]). *)
    } (** A compound type of [kind] consisting of [fields]. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** A typing enviromnent. *)
type t [@@deriving bin_io, compare, equal, hash, sexp]

(** The empty typing environment. *)
val empty : t

(** Returns [true] if the name is part of the ordinary-identifier namespace. *)
val in_ordinary : t -> string -> bool

(** Add a tag type to the environment. *)
val add_tag : t -> name:string -> tag -> t Or_error.t

(** Add an enum element to the environment.

    [name] is the name of the enum item, [tag] is its owning typename,
    and [value] is its integer value.
*)
val add_enum_element : t -> name:string -> tag:string -> value:int64 -> t Or_error.t

(** Add a typedef to the environment. *)
val add_typedef : t -> name:string -> Texpr.ty -> t Or_error.t

(** Add a function to the environment. *)
val add_func : t -> name:string -> Texpr.ty -> t Or_error.t

(** Add a global variable to the environment. *)
val add_global : t -> name:string -> Texpr.ty -> t Or_error.t

(** Add a local variable (or parameter) binding to the innermost
    scope.

    Locals can shadow file-scope identifiers and outer-scope locals.
*)
val add_local : t -> name:string -> Texpr.ty -> t

(** Same as [add_local], but returns an error if [name] is already
    bound in the {e innermost} scope. Outer-scope bindings of the same
    name are legal shadows and do not conflict. *)
val strict_add_local : t -> name:string -> Texpr.ty -> t Or_error.t

(** Push a fresh, empty innermost scope onto the local-binding stack.

    Bindings added after this only shadow, never collide with, the
    bindings of enclosing scopes. The matching pop is performed by the
    caller restoring an earlier environment snapshot.
*)
val push_scope : t -> t

(** Looks up the tag type by name. *)
val find_tag : t -> string -> tag option

(** Looks up the enum element by name. *)
val find_enum_element : t -> string -> enum_element option

(** Looks up the typedef by name. *)
val find_typedef : t -> string -> Texpr.ty option

(** Looks up the function type by name. *)
val find_func : t -> string -> Texpr.ty option

(** Looks up the global variable type by name. *)
val find_global : t -> string -> Texpr.ty option

(** Looks up the local variable type by name. *)
val find_local : t -> string -> Texpr.ty option

(** Performs a membership test for the tag type by name. *)
val has_tag : t -> string -> bool

(** Performs a membership test for the enum element by name. *)
val has_enum_element : t -> string -> bool

(** Performs a membership test for the typedef by name. *)
val has_typedef : t -> string -> bool

(** Performs a membership test for the function type by name. *)
val has_func : t -> string -> bool

(** Performs a membership test for the global variable type by name. *)
val has_global : t -> string -> bool

(** Performs a membership test for the local variable type by name. *)
val has_local : t -> string -> bool

(** All tag types in the environment. *)
val tags : t -> (string * tag) Sequence.t

(** All enum constants in the environment. *)
val enum_elements: t -> (string * enum_element) Sequence.t

(** All typedefs in the environment. *)
val typedefs : t -> (string * Texpr.ty) Sequence.t

(** All function types in the environment. *)
val funcs : t -> (string * Texpr.ty) Sequence.t

(** All global variable types in the environment. *)
val globals : t -> (string * Texpr.ty) Sequence.t

(** All local variable (and parameter) bindings currently in scope. *)
val locals : t -> (string * Texpr.ty) Sequence.t

(** Returns [true] if the provided tag type exists in the environment
    and has a complete definition. *)
val is_tag_complete : t -> string -> bool

(** [normalize env ty] resolves typedef names in [ty] to their underlying
    types (composing cv-qualifiers), leaving struct/union/enum tags
    intact. Idempotent. *)
val normalize : t -> Texpr.ty -> Texpr.ty
