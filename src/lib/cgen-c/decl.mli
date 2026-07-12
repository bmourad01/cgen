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
      attrs    : 'a Attr.raws;
      (** Attributes, including [_Noreturn] folded in as {!Attr.Noreturn}. *)
    } (** A function declaration or definition. *)
  | Dvar of {
      name    : string;
      ty      : 'a Expr.ty;
      init    : 'a Expr.init option;
      storage : Stmt.storagecls;
      tls     : bool;
      (** Set when [_Thread_local] was used. *)
      attrs   : 'a Attr.raws;
    } (** A global object declaration or definition. *)
  | Dtype of 'a Tydecl.t
  (** A struct/union/enum/typedef definition (see {!Tydecl}). *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors} *)

(** A function declaration or definition.

    [variadic] and [inline] default to [false]; [attrs] defaults to empty.

    [storage] defaults to [SCdefault].
*)
val fun_ :
  ?variadic:bool ->
  ?body:'a Stmt.t ->
  ?storage:Stmt.storagecls ->
  ?inline:bool ->
  ?attrs:'a Attr.raws ->
  name:string ->
  params:'a param list ->
  ret:'a Expr.ty ->
  ann:'a ->
  unit ->
  'a t

(** A global object declaration or definition.

    [storage] defaults to [SCdefault].
    [tls] defaults to [false].
    [attrs] defaults to empty.
*)
val var :
  ?init:'a Expr.init ->
  ?storage:Stmt.storagecls ->
  ?tls:bool ->
  ?attrs:'a Attr.raws ->
  name:string ->
  ty:'a Expr.ty ->
  ann:'a ->
  unit ->
  'a t

(** Wrap a type declaration (see {!Tydecl}) as a top-level declaration. *)
val of_tydecl : 'a Tydecl.t -> 'a t

(** A function parameter. *)
val param : ?name:string -> ty:'a Expr.ty -> unit -> 'a param

(** {1 Pretty printers} *)

(** Renders a function parameter (type and optional name). *)
val pp_param : Format.formatter -> 'a param -> unit

(** Renders a top-level declaration in C syntax.

    Function definitions render their body inline.

    Struct/union and enum bodies are indented two spaces.
*)
val pp : Format.formatter -> 'a t -> unit

(** [to_string d] is [pp] rendered to a string. *)
val to_string : 'a t -> string
