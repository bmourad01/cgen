(** Untyped top-level declarations.

    Parameterized over an annotation type ['a] in the
    "Trees That Grow" style: a parser supplies [Location.t],
    while hand-written ASTs can supply [unit].
*)

(** A function parameter declaration. *)
type 'a param = {
  pname : string option;
  pty   : 'a Expr.ty;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A field in a [struct] or [union]. [fbits] is the bit-field width,
    or [None] for an ordinary field. *)
type 'a field = {
  fname : string;
  fty   : 'a Expr.ty;
  fbits : 'a Expr.t option;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** An [enum] enumerator. [eivalue] is the explicit value expression,
    or [None] to let the previous value determine it. *)
type 'a eitem = {
  einame  : string;
  eivalue : 'a Expr.t option;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A top-level declaration node paired with its annotation. *)
type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Dfun of {
      name     : string;
      params   : 'a param list;
      variadic : bool;
      ret      : 'a Expr.ty;
      body     : 'a Stmt.t option;
      (** Function body. [None] denotes a prototype-only declaration. *)
      storage  : Stmt.storagecls;
      inline   : bool;
      noreturn : bool;
    } (** A function declaration or definition. *)
  | Dvar of {
      name    : string;
      ty      : 'a Expr.ty;
      init    : 'a Expr.init option;
      storage : Stmt.storagecls;
      tls     : bool;
      (** Set when [_Thread_local] was used. *)
    } (** A global object declaration or definition. *)
  | Dcompound of {
      kind   : Type.compound;
      tag    : string;
      fields : 'a field list;
    } (** A [struct] or [union] definition. *)
  | Denum of {
      tag   : string;
      items : 'a eitem list;
    } (** An [enum] definition. *)
  | Dtypedef of {
      name : string;
      ty   : 'a Expr.ty;
    } (** A [typedef] introducing [name] as an alias for [ty]. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors} *)

(** A function declaration or definition.

    [variadic], [inline], and [noreturn] default to [false].

    [storage] defaults to [SCdefault].
*)
val fun_ :
  ?variadic:bool ->
  ?body:'a Stmt.t ->
  ?storage:Stmt.storagecls ->
  ?inline:bool ->
  ?noreturn:bool ->
  name:string ->
  params:'a param list ->
  ret:'a Expr.ty ->
  ann:'a ->
  unit ->
  'a t

(** A global object declaration or definition.

    [storage] defaults to [SCdefault].

    [tls] defaults to [false].
*)
val var :
  ?init:'a Expr.init ->
  ?storage:Stmt.storagecls ->
  ?tls:bool ->
  name:string ->
  ty:'a Expr.ty ->
  ann:'a ->
  unit ->
  'a t

(** A [struct] or [union] definition. *)
val compound :
  kind:Type.compound ->
  tag:string ->
  fields:'a field list ->
  ann:'a ->
  'a t

(** An [enum] definition. *)
val enum : tag:string -> items:'a eitem list -> ann:'a -> 'a t

(** A [typedef] introducing [name] as an alias for [ty]. *)
val typedef : name:string -> ty:'a Expr.ty -> ann:'a -> 'a t

(** A function parameter. *)
val param : ?name:string -> ty:'a Expr.ty -> unit -> 'a param

(** A struct/union field. [bits] is the bit-field width when
    declared as one. *)
val field :
  ?bits:'a Expr.t ->
  name:string ->
  ty:'a Expr.ty ->
  unit ->
  'a field

(** An [enum] enumerator. *)
val eitem : ?value:'a Expr.t -> name:string -> unit -> 'a eitem

(** {1 Pretty printers} *)

(** Renders a function parameter (type and optional name). *)
val pp_param : Format.formatter -> 'a param -> unit

(** Renders a struct/union field declaration with trailing
    semicolon (and bit-field width when present). *)
val pp_field : Format.formatter -> 'a field -> unit

(** Renders a single enumerator (name with optional value). *)
val pp_eitem : Format.formatter -> 'a eitem -> unit

(** Renders a top-level declaration in C syntax.

    Function definitions render their body inline.

    Struct/union and enum bodies are indented two spaces.
*)
val pp : Format.formatter -> 'a t -> unit

(** [to_string d] is [pp] rendered to a string. *)
val to_string : 'a t -> string
