(** Untyped statements.

    Parameterized over an annotation type ['a] in the
    "Trees That Grow" style: a parser supplies [Location.t],
    while hand-written ASTs can supply [unit].
*)

(** Storage-class specifier. [SCdefault] denotes no explicit
    specifier. *)
type storagecls =
  | SCdefault
  | SCauto
  | SCstatic
  | SCregister
  | SCextern
[@@deriving bin_io, compare, equal, hash, sexp]

(** A local (block-scope) declaration.

    [ldann] carries the annotation for the initializer.
*)
type 'a localdecl = {
  ldname    : string;
  ldty      : 'a Expr.ty;
  ldinit    : 'a Expr.init option;
  ldstorage : storagecls;
  ldattrs   : 'a Attr.raws;
  ldann     : 'a;
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A statement node paired with its annotation. *)
type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Sblock of 'a blkitem list
  (** A compound statement: a sequence of declarations and
      statements in a new block scope. *)
  | Sif of {
      cond  : 'a Expr.t;
      then_ : 'a t;
      else_ : 'a t option;
    } (** An [if] statement. *)
  | Swhile of {
      cond : 'a Expr.t;
      body : 'a t;
    } (** A [while] loop. *)
  | Sdowhile of {
      body : 'a t;
      cond : 'a Expr.t;
    } (** A [do]-[while] loop. *)
  | Sfor of {
      init : 'a forinit option;
      cond : 'a Expr.t option;
      step : 'a Expr.t option;
      body : 'a t;
    } (** A [for] loop. Each of [init], [cond], and [step] is
          optional, matching C's omitted clauses. *)
  | Sswitch of {
      expr : 'a Expr.t;
      body : 'a t;
    } (** A [switch] statement. *)
  | Scase of {
      value : 'a Expr.t;
      body  : 'a t;
    } (** A [case] label and the statement it labels. *)
  | Sdefault of 'a t
  (** A [default] label and the statement it labels. *)
  | Slabel of {
      name : string;
      body : 'a t;
    } (** A named label and the statement it labels. *)
  | Sgoto of string
  (** A [goto] to a named label. *)
  | Sgotoind of 'a Expr.t
  (** A computed [goto *e] (GNU extension): jump to the label whose address
      [e] holds. *)
  | Sbreak
  (** A [break] statement. *)
  | Scontinue
  (** A [continue] statement. *)
  | Sreturn of 'a Expr.t option
  (** A [return] statement, optionally with a value. *)
  | Sexpr of 'a Expr.t
  (** An expression statement. *)
  | Snull
  (** The null statement (a lone [;]). *)

and 'a forinit =
  | FIexpr of 'a Expr.t
  (** An expression initializer (pre-C99 style). *)
  | FIdecl of 'a localdecl list
  (** A declaration initializer (C99 [for (int i = 0; ...)]). *)

and 'a blkitem =
  | Bstmt of 'a t
  (** A statement appearing in a block. *)
  | Bdecl of 'a localdecl list
  (** A declaration appearing in a block. A single declaration
      specifier may introduce multiple declarators (e.g.
      [int x, y = 0;]). *)
  | Btype of 'a Tydecl.t list
  (** Block-scope struct/union/enum/typedef definitions introduced by a
      declaration specifier (see {!Tydecl}). *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors} *)

(** A compound statement. *)
val block : 'a blkitem list -> ann:'a -> 'a t

(** An [if] statement. *)
val if_ :
  ?else_:'a t ->
  cond:'a Expr.t ->
  then_:'a t ->
  ann:'a ->
  unit ->
  'a t

(** A [while] loop. *)
val while_ : cond:'a Expr.t -> body:'a t -> ann:'a -> 'a t

(** A [do]-[while] loop. *)
val dowhile : body:'a t -> cond:'a Expr.t -> ann:'a -> 'a t

(** A [for] loop.

    Each of [init], [cond], and [step] is optional.
*)
val for_ :
  ?init:'a forinit ->
  ?cond:'a Expr.t ->
  ?step:'a Expr.t ->
  body:'a t ->
  ann:'a ->
  unit ->
  'a t

(** A [switch] statement. *)
val switch : expr:'a Expr.t -> body:'a t -> ann:'a -> 'a t

(** A [case] label and the statement it labels. *)
val case : value:'a Expr.t -> body:'a t -> ann:'a -> 'a t

(** A [default] label and the statement it labels. *)
val default : 'a t -> ann:'a -> 'a t

(** A named label and the statement it labels. *)
val label : name:string -> body:'a t -> ann:'a -> 'a t

(** A [goto] to a named label. *)
val goto : string -> ann:'a -> 'a t

(** A computed [goto *e] (GNU extension). *)
val gotoind : 'a Expr.t -> ann:'a -> 'a t

(** A [break] statement. *)
val break : ann:'a -> 'a t

(** A [continue] statement. *)
val continue : ann:'a -> 'a t

(** A [return] statement, optionally with a value. *)
val return : ?value:'a Expr.t -> ann:'a -> unit -> 'a t

(** An expression statement. *)
val expr : 'a Expr.t -> ann:'a -> 'a t

(** The null statement. *)
val null : ann:'a -> 'a t

(** A local declaration. [storage] defaults to [SCdefault]. *)
val localdecl :
  ?init:'a Expr.init ->
  ?storage:storagecls ->
  ?attrs:'a Attr.raws ->
  name:string ->
  ty:'a Expr.ty ->
  ann:'a ->
  unit ->
  'a localdecl

(** {1 Pretty printers} *)

(** Renders a storage-class specifier with a trailing space.
    [SCdefault] renders as the empty string. *)
val pp_storagecls : Format.formatter -> storagecls -> unit

(** Renders a single local declaration: storage class, declarator,
    and optional initializer. Emits no trailing semicolon. *)
val pp_localdecl : Format.formatter -> _ localdecl -> unit

(** Renders a statement in C syntax. *)
val pp : Format.formatter -> _ t -> unit

(** [to_string s] is [pp] rendered to a string. *)
val to_string : _ t -> string

(** Renders a statement as the inline body of an outer construct,
    {b assuming an outer [@\[<v 2>] vbox is open}. Blocks are
    emitted K&R-style ([{ items }], with the closing brace at the
    outer indent via a [@;<0 -2>] break); non-blocks are emitted on
    a fresh line indented by two ([@,statement]).

    Used by callers that need to render their own prefix on the same
    line as the body's opening [{], most notably function definitions
    in {!Decl.pp}.
*)
val pp_inline_body : Format.formatter -> _ t -> unit
