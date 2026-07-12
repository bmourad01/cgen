(** C types.

    The type is parameterized by ['e], the representation of
    expressions used in array sizes. The untyped surface AST
    instantiates ['e] with [_ Expr.t]; the typed AST uses [Texpr.t].
*)

(** Signedness of an integer type. *)
type sign =
  | Ssigned
  | Sunsigned
[@@deriving bin_io, compare, equal, hash, sexp]

(** Standard integer types (excluding [_Bool] and [char], which are
    represented as separate bases). *)
type ity =
  | Ichar of sign
  | Ishort of sign
  | Iint of sign
  | Ilong of sign
  | Ilonglong of sign
[@@deriving bin_io, compare, equal, hash, sexp]

(** Signedness of a standard integer type. *)
val ity_sign : ity -> sign

(** Standard floating-point types. *)
type fty =
  | Ffloat
  | Fdouble
[@@deriving bin_io, compare, equal, hash, sexp]

(** Base (atomic) types. *)
type base =
  | Bvoid
  | Bbool
  | Bchar
  | Bint of ity
  | Bfloat of fty
[@@deriving bin_io, compare, equal, hash, sexp]

(** CV-qualifiers ([const], [volatile]). *)
module Cv : sig
  type t = private int [@@deriving bin_io, compare, equal, hash, sexp]

  (** No qualifiers. *)
  val empty : t

  (** [const]. *)
  val const : t

  (** [volatile]. *)
  val volatile : t

  (** [const volatile]. *)
  val const_volatile : t

  (** Union of twp CV-qualifiers. *)
  val combine : t -> t -> t

  val is_const : t -> bool
  val is_volatile : t -> bool
  val is_const_volatile : t -> bool

  val pp : Format.formatter -> t -> unit
end

type cv = Cv.t [@@deriving bin_io, compare, equal, hash, sexp]

(** Tags of compound types (those introduced by [struct] or [union]). *)
type compound = [
  | `struct_
  | `union
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Tags of types declared via a [struct], [union], or [enum]
    specifier. *)
type tag = [
  | compound
  | `enum
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Tags of types referred to by a name: tagged types plus
    [typedef]-introduced names. *)
type named = [
  | tag
  | `typedef
] [@@deriving bin_io, compare, equal, hash, sexp]

(** A C type parameterized by the expression representation ['e]
    used in array sizes. *)
type 'e t =
  | Tbase of {
      base : base;
      cv   : cv;
    } (** A base (atomic) type with cv-qualifiers. *)
  | Tptr of {
      pointee  : 'e t;
      restrict : bool;
      (** Set when the pointer was declared [restrict]. *)
      cv       : cv;
    } (** A pointer type. *)
  | Tarray of {
      elem     : 'e t;
      size     : 'e option;
      (** Array length. [None] denotes an incomplete array. *)
      cv       : cv;
      restrict : bool;
      (** Only meaningful on a parameter: the type qualifiers ([cv]) and
          [restrict] inside its brackets (C99 §6.7.6.3), which qualify the
          pointer it decays to. *)
      static_  : bool;
      (** Only meaningful on a parameter: the [static] in [a\[static n\]]
          (C99 §6.7.6.3), asserting the argument points to at least [size]
          elements. It has no home on the decayed pointer, so it is dropped
          there; cgen does not otherwise use it. *)
    } (** An array type. *)
  | Tnamed of {
      kind : named;
      name : string;
      cv   : cv;
    } (** A type referenced by name: a tagged type ([struct], [union],
          [enum]) or a [typedef]-introduced alias. *)
  | Tfun of {
      result   : 'e t;
      params   : 'e param list option;
      (** [None] denotes a K&R declarator (parameter information is
          unknown). [Some \[\]] is the zero-argument prototype
          (written [(void)] in source). [Some \[...\]] is a normal
          prototype. *)
      variadic : bool;
    } (** A function type. Function types are not cv-qualified. *)

(** A function parameter: an optional name and a type. *)
and 'e param = {
  pname : string option;
  ptype : 'e t;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors}

    The optional [cv] argument defaults to no qualifiers.
*)

(** The [void] type. *)
val void : ?cv:cv -> unit -> _ t

(** The [_Bool] type. *)
val bool_ : ?cv:cv -> unit -> _ t

(** The plain [char] type. *)
val plain_char_ : ?cv:cv -> unit -> _ t

(** An explicitly signed [char] type. *)
val char_ : ?cv:cv -> sign -> _ t

(** [int_ ?cv ?sign ()] is the [int] type. [sign] defaults to
    [Ssigned]. *)
val int_ : ?cv:cv -> ?sign:sign -> unit -> _ t

(** [short_ ?cv ?sign ()] is the [short] type. [sign] defaults to
    [Ssigned]. *)
val short_ : ?cv:cv -> ?sign:sign -> unit -> _ t

(** [long_ ?cv ?sign ()] is the [long] type. [sign] defaults to
    [Ssigned]. *)
val long_ : ?cv:cv -> ?sign:sign -> unit -> _ t

(** [longlong_ ?cv ?sign ()] is the [long long] type. [sign] defaults to
    [Ssigned]. *)
val longlong_ : ?cv:cv -> ?sign:sign -> unit -> _ t

(** [float_ ?cv ()] is the [float] type. *)
val float_ : ?cv:cv -> unit -> _ t

(** [double_ ?cv ()] is the [double] type. *)
val double_ : ?cv:cv -> unit -> _ t

(** [ptr ?cv ?restrict pointee] is a pointer to [pointee]. *)
val ptr : ?cv:cv -> ?restrict:bool -> 'e t -> 'e t

(** [array ?cv ?restrict ?static_ ?size elem] is an array of [elem].

    A missing [size] denotes an incomplete array type.

    [cv], [restrict], and [static_] carry the bracket qualifiers of an
    array parameter (see {!Tarray}).
*)
val array : ?cv:cv -> ?restrict:bool -> ?static_:bool -> ?size:'e -> 'e t -> 'e t

val struct_ : ?cv:cv -> string -> _ t
val union_ : ?cv:cv -> string -> _ t
val enum_ : ?cv:cv -> string -> _ t
val typedef_ : ?cv:cv -> string -> _ t

(** [fun_ ~result ~params ?variadic ()] is a prototyped function
    type.

    An empty [params] corresponds to source [(void)].

    [variadic] defaults to [false].
*)
val fun_ :
  result:'e t ->
  params:'e param list ->
  ?variadic:bool ->
  unit ->
  'e t

(** [fun_kr result] is a K&R (unprototyped) function type.

    With K&R functions, the parameter information is unknown.
    K&R functions cannot be variadic.
*)
val fun_kr : 'e t -> 'e t

(** {1 Predicates} *)

val is_void : _ t -> bool

(** Integer types in the C99 sense: [_Bool], [char], the standard
    integer types, and enumerated types. *)
val is_integer : _ t -> bool

val is_floating : _ t -> bool

(** Arithmetic types: integer or floating. *)
val is_arithmetic : _ t -> bool

val is_pointer : _ t -> bool

(** Scalar types: arithmetic or pointer. *)
val is_scalar : _ t -> bool

val is_array : _ t -> bool
val is_function : _ t -> bool

(** True for [struct] and [union] tagged types. Excludes [enum]. *)
val is_compound : _ t -> bool

(** {1 cv-qualifier manipulation} *)

(** cv-qualifier set on the outermost form. Function types are
    unqualified by definition and return [Cv.mask]. *)
val cv_of : _ t -> cv

(** [with_cv cv t] replaces the outermost cv-qualifier set on [t].
    On function types, [t] is returned unchanged. *)
val with_cv : cv -> 'e t -> 'e t

(** [unqualified t] strips the outermost cv-qualifiers. *)
val unqualified : 'e t -> 'e t

(** {1 Pretty printers}

    [t] is parameterized by the array-size expression type ['e],
    so the printers take an expression printer explicitly.
*)

val pp_sign : Format.formatter -> sign -> unit
val pp_ity : Format.formatter -> ity -> unit
val pp_fty : Format.formatter -> fty -> unit
val pp_base : Format.formatter -> base -> unit

(** Renders [t] as a C abstract declarator (no name).

    The type specifier followed by the declarator fragments (pointers,
    arrays, function-parameter lists), with parentheses inserted where
    needed for correct binding.
*)
val pp_with :
  (Format.formatter -> 'e -> unit) ->
  Format.formatter -> 'e t -> unit

(** Like [pp_with], but places [name] in declarator position so the
    result is a complete C declaration prefix.

    An empty [name] is equivalent to [pp_with]
*)
val pp_named_with :
  (Format.formatter -> 'e -> unit) ->
  Format.formatter -> 'e t -> name:string -> unit

(** Renders only the declarator portion of [t] (no leading type
    specifier), with [name] in declarator position.

    Useful when emitting multiple init-declarators that share a
    single declaration specifier, as in [int x, *y = NULL;].
*)
val pp_declarator_with :
  (Format.formatter -> 'e -> unit) ->
  Format.formatter -> 'e t -> name:string -> unit
