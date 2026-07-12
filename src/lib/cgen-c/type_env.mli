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
      fields : Tdecl.field list option;
      (** [None] for an incomplete (forward-declared) tag; [Some fields]
          once defined. *)
      attrs  : Attr.set;
      (** Attributes on the aggregate (e.g. [packed], [aligned]). *)
    } (** A compound type of [kind]. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** A typing enviromnent. *)
type t [@@deriving bin_io, compare, equal, hash, sexp]

(** The empty typing environment. *)
val empty : t

(** [add_tag env ~name info] registers a tag declaration whose source name
    is [name] in the innermost scope, returning the updated environment and
    the {e display name} the tag was given.

    The display name is [name] itself unless a tag of that name already
    exists (a shadow of an enclosing tag, or a sibling block's tag), in
    which case it is disambiguated so the two distinct types do not collide
    in the flat lowering namespace.

    A redeclaration in the {e same} scope completes a forward declaration,
    accepts a redundant re-declaration, or is rejected as an incompatible
    redefinition, preserving the display name.

    Callers record the returned display name in the elaborated type (via
    {!resolve_tag} at reference sites) and in any emitted declaration.
*)
val add_tag : t -> name:string -> tag -> (t * string) Or_error.t

(** [resolve_tag env name] is the display name that the source tag [name]
    currently denotes, following the lexical scope stack, or [None] if the
    tag is undeclared in every visible scope (the caller decides whether
    that is a forward reference to declare incomplete, or an error). *)
val resolve_tag : t -> string -> string option

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

(** Push a fresh, empty innermost scope onto the local-binding and tag
    resolution stacks.

    Bindings added after this only shadow, never collide with, the
    bindings of enclosing scopes. The matching pop is performed by the
    caller restoring an earlier environment snapshot.
*)
val push_scope : t -> t

(** [exit_block ~saved env] leaves a block scope.

    It drops the block's locals, enum constants, typedefs, and tag {e name
    bindings} (taken from [saved], the pre-block environment) but keeps
    every tag {e definition}, which the lowering needs globally, keyed by
    the identity {!add_tag} assigned.
*)
val exit_block : saved:t -> t -> t

(** Looks up a tag definition by its display name (the name carried by an
    already-elaborated type, i.e. what {!add_tag}/{!resolve_tag} return,
    {e not} a raw source name). *)
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

(** Performs a membership test for a tag definition by its display name
    (see {!find_tag}). *)
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

(** Returns [true] if a tag with the given display name exists in the
    environment and has a complete definition. *)
val is_tag_complete : t -> string -> bool

(** [normalize env ty] resolves typedef names in [ty] to their underlying
    types (composing cv-qualifiers), leaving struct/union/enum tags
    intact. Idempotent. *)
val normalize : t -> Texpr.ty -> Texpr.ty

(** [incomplete_object_type env ty] is the tag of an incomplete [struct]
    or [union] that makes [ty] unusable as an object type (directly, or
    as an array element), or [None] if [ty] is a complete object type. *)
val incomplete_object_type : t -> Texpr.ty -> string option
