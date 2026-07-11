(** Typed (elaborated) statements.

    Produced by elaboration from [Stmt.t]. Side-effecting work
    (assignments, increment/decrement, calls) is factored out of
    expressions into explicit [instr]s, so [Texpr.t] stays pure.
*)

open Core

(** A local (block-scope) declaration. *)
type localdecl = {
  name  : string;
  ty    : Texpr.ty;
  init  : Texpr.init option;
  align : int option;
  (** An over-alignment requested by [__attribute__((aligned(n)))], if any. *)
} [@@deriving bin_io, compare, equal, hash, sexp]

(** A side-effecting instruction. *)
type instr =
  | Iassign of {
      lval : Texpr.tlval;
      expr : Texpr.t;
    } (** A scalar assignment ([lval = expr]). *)
  | Icall of {
      lval : Texpr.tlval option;
      fn   : Texpr.t;
      args : Texpr.t list;
    } (** A function call, optionally storing the result in [lval]. *)
  | Ibuiltin of {
      lval : Texpr.tlval option;
      name : string;
      args : Texpr.t list;
    } (** A compiler builtin (e.g. [__builtin_va_arg]), optionally
          storing its result in [lval]. [name] is the full builtin
          spelling; lowering dispatches on it. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** The init clause of a [for] loop. *)
type forinit =
  | FIexpr of instr list
  (** A list of side-effecting instructions. *)
  | FIdecl of localdecl
  (** A single local declaration. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** An item in a block. *)
type blkitem =
  | Bstmt of t
  (** A statement appearing in a block. *)
  | Bdecl of localdecl
  (** A local declaration appearing in a block. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** A typed statement. *)
and t =
  | Sblock of blkitem list
  (** A compound statement. *)
  | Sif of {
      cond  : Texpr.t;
      then_ : t;
      else_ : t option;
    } (** An [if] statement. *)
  | Swhile of {
      cond : Texpr.t;
      body : t;
    } (** A [while] loop. *)
  | Sdowhile of {
      body : t;
      cond : Texpr.t;
    } (** A [do]-[while] loop. *)
  | Sfor of {
      init : forinit option;
      cond : Texpr.t option;
      step : instr list;
      body : t;
    } (** A [for] loop. *)
  | Sswitch of {
      expr : Texpr.t;
      body : t;
    } (** A [switch] statement. *)
  | Scase of {
      value : Cgen_utils.Bv.t;
      body  : t;
    } (** A [case] label and the statement it labels. The case
          value is the resolved integer constant. *)
  | Sdefault of t
  (** A [default] label and the statement it labels. *)
  | Slabel of {
      name : string;
      body : t;
    } (** A named label and the statement it labels. *)
  | Sgoto of string
  | Sgotoind of Texpr.t
  (** A [goto] to a named label. *)
  | Sbreak
  (** A [break] statement. *)
  | Scontinue
  (** A [continue] statement. *)
  | Sreturn of Texpr.t option
  (** A [return] statement, optionally with a value. *)
  | Sinstr of instr list
  (** A sequence of side-effecting instructions used as a statement
      (the elaboration of an expression statement). *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors} *)

(** A local declaration. *)
val localdecl :
  ?init:Texpr.init ->
  ?align:int ->
  name:string ->
  ty:Texpr.ty ->
  unit ->
  localdecl

(** {2 Instructions} *)

(** An assignment instruction. *)
val assign : lval:Texpr.tlval -> expr:Texpr.t -> instr

(** A call instruction, with an optional destination lvalue. *)
val call :
  ?lval:Texpr.tlval ->
  fn:Texpr.t ->
  args:Texpr.t list ->
  unit ->
  instr

(** A builtin instruction, with an optional destination lvalue. *)
val builtin :
  ?lval:Texpr.tlval ->
  name:string ->
  args:Texpr.t list ->
  unit ->
  instr

(** {2 For-init clauses} *)

(** An expression-style [for] initializer. *)
val fi_expr : instr list -> forinit

(** A declaration-style [for] initializer. *)
val fi_decl : localdecl -> forinit

(** {2 Block items} *)

(** Wrap a statement as a block item. *)
val bstmt : t -> blkitem

(** Wrap a local declaration as a block item. *)
val bdecl : localdecl -> blkitem

(** {2 Statements} *)

(** A compound statement. *)
val block : blkitem list -> t

(** An [if] statement. *)
val if_ :
  ?else_:t ->
  cond:Texpr.t ->
  then_:t ->
  unit ->
  t

(** A [while] loop. *)
val while_ : cond:Texpr.t -> body:t -> t

(** A [do]-[while] loop. *)
val dowhile : body:t -> cond:Texpr.t -> t

(** A [for] loop. *)
val for_ :
  ?init:forinit ->
  ?cond:Texpr.t ->
  step:instr list ->
  body:t ->
  unit ->
  t

(** A [switch] statement. *)
val switch : expr:Texpr.t -> body:t -> t

(** A [case] label and the statement it labels. *)
val case : value:Cgen_utils.Bv.t -> body:t -> t

(** A [default] label and the statement it labels. *)
val default : t -> t

(** A named label and the statement it labels. *)
val label : name:string -> body:t -> t

(** A [goto] to a named label. *)
val goto : string -> t
val gotoind : Texpr.t -> t

(** A [break] statement. *)
val break : t

(** A [continue] statement. *)
val continue : t

(** A [return] statement, optionally with a value. *)
val return : ?value:Texpr.t -> unit -> t

(** A sequence of side-effecting instructions used as a statement. *)
val instr : instr list -> t

(** {1 Pretty printers} *)

(** Renders a local declaration: type, name, optional initializer.
    No trailing semicolon. *)
val pp_localdecl : Format.formatter -> localdecl -> unit

(** Renders a side-effecting instruction (no trailing semicolon). *)
val pp_instr : Format.formatter -> instr -> unit

(** Renders a statement in C syntax using [Format]'s vertical boxes,
    so the output composes inside an enclosing box. *)
val pp : Format.formatter -> t -> unit

(** [to_string s] is [pp] rendered to a string. *)
val to_string : t -> string

(** Renders a statement as the inline body of an outer construct,
    {b assuming an outer [@\[<v 2>] vbox is open}. See
    {!Stmt.pp_inline_body}. *)
val pp_inline_body : Format.formatter -> t -> unit
