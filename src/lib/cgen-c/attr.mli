(** GNU C attributes as a first-class, queryable representation.

    Attributes exist in two forms, mirroring the untyped/typed split of the
    rest of the frontend:

    - {!type-raw} is an attribute {e as parsed}: a name and a list of argument
      {e expressions}, uninterpreted. This is what {!Decl} carries.
    - {!t} is the {e resolved} attribute: elaboration folds each argument
      expression to a constant and calls {!of_gnu} to interpret it. This is
      what {!Tdecl}, {!Type_env}, and layout consume.
*)

(** A resolved attribute argument. *)
type arg =
  | Aint  of int64
  (** A folded integer constant *)
  | Astr  of string
  (** A string literal *)
  | Aname of string
  (** A bare identifier (a mode, type, function, or visibility name) *)
[@@deriving bin_io, compare, equal, hash, sexp]

type visibility =
  | Default
  | Hidden
  | Internal
  | Protected
[@@deriving bin_io, compare, equal, hash, sexp]

(** A single attribute.

    Recognized attributes are modeled directly. Anything unrecognized is
    preserved as [Other].

    GNU spellings are normalized by stripping a leading and trailing [__] before
    matching, so [__aligned__] is the same as [aligned].
*)
type t =
  (* Layout. *)
  | Aligned of int option
  (** [aligned] (=[None]) or [aligned(n)]. *)
  | Packed
  (* Function & optimization hints. *)
  | Noreturn
  | Always_inline
  | Noinline
  | Pure
  | Const
  (** [__attribute__((const))], not the qualifier. *)
  | Malloc
  | Cold
  | Hot
  | Used
  | Unused
  | Deprecated of string option
  | Warn_unused_result
  | Returns_twice
  | Nothrow
  (* Linkage & emission. *)
  | Section of string
  | Visibility of visibility
  | Weak
  | Alias of string
  | Constructor of int option
  | Destructor of int option
  (* Types & aliasing. *)
  | Transparent_union
  | May_alias
  | Mode of string
  | Nonnull of int list
  (** Empty list implies all pointer arguments. *)
  | Format of string * int * int
  (** archetype, format-index, first-vararg. *)
  | Cleanup of string
  | Other of string * arg list
  (** Parsed and carried, not interpreted. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** A collection of resolved attributes, in the order written. *)
type set = t list [@@deriving bin_io, compare, equal, hash, sexp]

val empty : set
val is_empty : set -> bool
val of_list : t list -> set
val to_list : set -> t list
val add : t -> set -> set
val union : set -> set -> set

(** {1 The parsed (untyped) form}

    An attribute as written, before its argument expressions are folded to
    constants. Parameterized over the annotation like the rest of the untyped
    AST.
*)

(** One attribute as parsed: its name and its argument expressions.

    Arguments are ordinary C expressions (with the caveat that they must
    be compile-time constant).
*)
type 'a raw = {
  rname : string;
  rargs : 'a Expr.t list;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A collection of parsed attributes, in the order written. *)
type 'a raws = 'a raw list [@@deriving bin_io, compare, equal, hash, sexp]

val raw : string -> 'a Expr.t list -> 'a raw

(** [of_gnu name args] builds a resolved attribute from a GNU attribute name
    and its {e resolved} arguments.

    [name] is normalized by stripping a surrounding [__]. Unrecognized names
    become {!Other}.
*)
val of_gnu : string -> arg list -> t

val exists  : set -> f:(t -> bool) -> bool
val find_map : set -> f:(t -> 'a option) -> 'a option

(** {2 Common typed queries} *)

val noreturn : set -> bool
val packed : set -> bool

(** The requested alignment in bytes, or [None] if there is no [aligned]
    attribute.

    A bare [aligned] (no argument) yields [Some 0], meaning "the target's
    maximum useful alignment".
*)
val alignment : set -> int option

(** The preferred section (e.g. [".text"] or [".data"]) for a declaration. *)
val section : set -> string option

val visibility : set -> visibility option
val weak : set -> bool
val alias : set -> string option
val used : set -> bool
val unused : set -> bool
val is_deprecated : set -> bool

val pp : Format.formatter -> t -> unit
val pp_set : Format.formatter -> set -> unit

(** Renders a parsed attribute set as a GNU [__attribute__((...))] specifier
    (empty renders nothing). Argument expressions render via {!Expr.pp}. *)
val pp_raws : Format.formatter -> 'a raws -> unit
