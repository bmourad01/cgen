(** Memory layout computation for C types.

    A [Layout.t] carries the typing environment, plus the precomputed
    layout maps it derives from it (sizes, field offsets, bit-field
    placements). The two layers are kept in lockstep: every tag
    introduced via {!add_tag} extends both the inner tenv and the
    layout maps in a single step, so callers never see a tenv with
    a tag whose layout hasn't been computed.

    Non-tag tenv mutators (typedefs, locals, etc.) just forward to
    the inner tenv since they don't affect layout.
*)

open Core

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
      Equals {!storage} unless the declared-type unit overlaps a normal member,
      in which case the access is narrowed to avoid it. *)
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

(** A precomputed layout table covering every complete compound tag
    in a typing environment. *)
type t [@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Construction} *)

(** [empty ~dmodel] is a layout with an empty typing environment. *)
val empty : dmodel:Data_model.t -> t

(** [create d tenv] computes layouts for every complete struct
    and union in [tenv] using the data model [d].

    Returns an error on layout cycles, incomplete value-typed fields,
    or other malformed compound definitions.
*)
val create : Data_model.t -> Type_env.t -> t Or_error.t

(** {1 Accessors} *)

(** The data model under which the layouts were computed. *)
val dmodel : t -> Data_model.t

(** The inner typing environment. *)
val tenv : t -> Type_env.t

(** {1 Tenv extension}

    Each function below extends the inner [Type_env.t] and (for
    [add_tag] of a complete struct/union) the layout maps in
    lockstep. *)

(** [add_tag t ~name tag] registers a tag declaration whose source name is
    [name], returning the updated layout and the display name assigned to
    the tag (see {!Type_env.add_tag}).

    For a complete [Tcompound] this also computes and stores its layout,
    offsets, and bit-field placements, keyed by the returned display name.
    Incomplete compounds and enums update only the tenv.
*)
val add_tag : t -> name:string -> Type_env.tag -> (t * string) Or_error.t

(** Register an enum element. *)
val add_enum_element :
  t -> name:string -> tag:string -> value:int64 -> t Or_error.t

(** Register a typedef. *)
val add_typedef : t -> name:string -> Texpr.ty -> t Or_error.t

(** Register a function. *)
val add_func : t -> name:string -> Texpr.ty -> t Or_error.t

(** Register a global variable. *)
val add_global : t -> name:string -> Texpr.ty -> t Or_error.t

(** Add a local variable (or parameter) binding.

    Locals can shadow file-scope identifiers.
*)
val add_local : t -> name:string -> Texpr.ty -> t

(** Same as [add_local] but errors if the name is already bound in the
    innermost scope.

    Outer-scope bindings of the same name are legal shadows.
*)
val strict_add_local : t -> name:string -> Texpr.ty -> t Or_error.t

(** Push a fresh, empty innermost scope onto the local-binding stack.

    Subsequent locals shadow, rather than collide with, enclosing
    scopes.

    The pop is implicit, with callers being expected to discard the
    scope by restoring an earlier environment.
*)
val push_scope : t -> t

(** Same as {!Type_env.exit_block}. *)
val exit_block : saved:t -> t -> t

(** {1 Layout queries} *)

(** [sizeof t ty] is the size of [ty] in bytes. *)
val sizeof : t -> Texpr.ty -> int Or_error.t

(** [alignof t ty] is the alignment requirement of [ty] in bytes. *)
val alignof : t -> Texpr.ty -> int Or_error.t

(** [offsetof t ~tag ~field] is the byte offset of [field] within
    the compound named [tag].

    Rejects bit fields per C99 §7.17.
*)
val offsetof : t -> tag:string -> field:string -> int Or_error.t

(** [bitfield_info t ~tag ~field] is the placement of bit field
    [field] within compound [tag]. *)
val bitfield_info : t -> tag:string -> field:string -> bitfield Or_error.t
