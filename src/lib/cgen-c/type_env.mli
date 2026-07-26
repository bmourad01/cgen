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

(** Placement of a bit field within its containing storage unit. *)
module Bitfield : sig
  type t [@@deriving bin_io, compare, equal, hash, sexp]

  (** Byte offset of the storage unit (relative to the enclosing
      compound). *)
  val storage : t -> int

  (** Bit offset of this field within its storage unit (zero-based). *)
  val offset : t -> int

  (** Width of the bit field in bits. *)
  val width : t -> int

  (** Byte offset of the integer used to read/write the field at run time.

      Equals {!storage} unless the declared-type unit overlaps a normal
      member, in which case the access is narrowed to avoid it.
  *)
  val access_storage : t -> int

  (** Width in bits of the run-time access integer. *)
  val access_bits : t -> int

  (** Whether the field must be accessed one byte at a time.

      [true] only for a [packed] field that straddles its storage unit, where
      no single in-bounds integer access covers it.

      {!access_storage} and {!access_bits} do not apply when this is [true].
  *)
  val bytewise : t -> bool
end

type bitfield = Bitfield.t [@@deriving bin_io, compare, equal, hash, sexp]

(** A typing environment.

    Besides the C name/type bindings, it carries the layout maps (sizes, field
    offsets, bit-field placements) derived from them. Registering a complete
    compound via {!add_tag} also computes its layout in the same step.
*)
type t [@@deriving bin_io, compare, equal, hash, sexp]

(** [empty ~dmodel] is the empty typing environment for data model [dmodel]. *)
val empty : dmodel:Data_model.t -> t

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

    For a complete [Tcompound] this additionally computes and stores its
    layout, offsets, and bit-field placements, keyed by the returned display
    name. Incomplete compounds and enums update only the name bindings.
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

(** {1 Layout queries} *)

(** The data model under which the layouts were computed. *)
val dmodel : t -> Data_model.t

(** [sizeof t ty] is the size of [ty] in bytes. *)
val sizeof : t -> Texpr.ty -> int Or_error.t

(** [alignof t ty] is the alignment requirement of [ty] in bytes. *)
val alignof : t -> Texpr.ty -> int Or_error.t

(** [offsetof t ~tag ~field] is the byte offset of [field] within the
    compound named [tag].

    Rejects bit fields per C99 §7.17.
*)
val offsetof : t -> tag:string -> field:string -> int Or_error.t

(** [bitfield_info t ~tag ~field] is the placement of bit field [field]
    within compound [tag]. *)
val bitfield_info : t -> tag:string -> field:string -> bitfield Or_error.t
