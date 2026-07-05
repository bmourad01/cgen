(** Typed (elaborated) expressions.

    Produced by elaboration from [Expr.t]. Every node carries its
    C type, and the operator alphabets exclude side-effecting forms
    (assignment, inc/dec, comma). Such forms are extracted to statements
    by elaboration.
*)

open Core

(** {1 Operators} *)

(** Pure binary operators: arithmetic, bitwise, and comparison. *)
type bop = [
  | Expr.barith
  | Expr.bbitwise
  | Expr.cmp
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pure unary operators plus pointer dereference. *)
type uop = [
  | Expr.uarith
  | Expr.ubitwise
  | Expr.ulogical
  | `deref
] [@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Expressions} *)

(** A node paired with its C type. *)
type 'n typed = {
  node : 'n;
  ty   : ty;
}

(** A C type. Array sizes embed [t] expressions, so [Type.t] is
    parameterized over [t]. *)
and ty = t Type.t

(** A typed rvalue expression. *)
and t = node typed

(** A typed lvalue expression. *)
and tlval = lval typed

and node =
  | Econst of Expr.const
  (** A literal constant. *)
  | Evar of string
  (** The value of a variable (a local, parameter, or global) after
      lvalue-to-rvalue conversion. *)
  | Efun of string
  (** A function designator; decays to a function pointer when used
      as an rvalue. *)
  | Eenum_const of {
      tag   : string;
      name  : string;
      value : Cgen_utils.Bv.t;
    }
  (** An enum constant with its [int] value already resolved. *)
  | Eunary of {
      op  : uop;
      arg : t;
    } (** A unary-operator application. *)
  | Ebinary of {
      op  : bop;
      lhs : t;
      rhs : t;
    } (** A binary-operator application. *)
  | Eindex of {
      arr : t;
      idx : t;
    } (** Array subscripting as an rvalue ([arr[idx]]). *)
  | Emember of {
      obj   : t;
      field : string;
    } (** Direct member access ([obj.field]). *)
  | Eaddrof of tlval
  (** Address-of an lvalue ([&lv]). *)
  | Ecast of {
      dst : ty;
      arg : t;
    } (** An explicit cast ([(dst)arg]). *)
  | Econd of {
      cond  : t;
      then_ : t;
      else_ : t;
    } (** The conditional operator ([cond ? then_ : else_]). *)
  | Ecompound of {
      ty   : ty;
      init : init;
    } (** A C99 compound literal ([(ty){init}]). *)

and lval =
  | Lvar of string
  (** A named object lvalue (local, parameter, or global). *)
  | Lderef of t
  (** Dereference of a pointer expression ([*p]). *)
  | Lmember of {
      lval  : tlval;
      field : string;
    } (** Member access producing an lvalue ([lv.field]). *)
  | Lindex of {
      lval  : tlval;
      index : t;
    } (** Array indexing producing an lvalue ([lv[index]]). *)

and init =
  | Isingle of t
  (** A single-expression initializer. *)
  | Iarray of init list
  (** A positional list of element initializers. *)
  | Istruct of (string * init) list
  (** A list of field-name/initializer pairs, in declaration order. *)
  | Iunion of {
      name : string;
      init : init;
    } (** A union initializer: which member is initialized and its
          value. *)
  | Ioverlay of {
      base : t;
      over : init;
    } (** A whole-aggregate value [base] refined by a partial struct
          initializer [over] (members designated after the whole value).
          Lowered as: store [base], then store the [over] members. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors for rvalues} *)

(** A literal constant. *)
val const : Expr.const -> ty:ty -> t

(** A variable's value. *)
val var : string -> ty:ty -> t

(** A function designator. *)
val fun_ : string -> ty:ty -> t

(** An enum constant with its resolved value. *)
val enum_const : tag:string -> name:string -> value:Cgen_utils.Bv.t -> ty:ty -> t

(** A unary-operator application. *)
val unary : op:uop -> arg:t -> ty:ty -> t

(** A binary-operator application. *)
val binary : op:bop -> lhs:t -> rhs:t -> ty:ty -> t

(** Array subscripting as an rvalue. *)
val index : arr:t -> idx:t -> ty:ty -> t

(** Direct member access. *)
val member : obj:t -> field:string -> ty:ty -> t

(** Address-of an lvalue. *)
val addrof : tlval -> ty:ty -> t

(** An explicit cast. The expression's type is taken from [dst]. *)
val cast : dst:ty -> arg:t -> t

(** The conditional operator. *)
val cond : cond:t -> then_:t -> else_:t -> ty:ty -> t

(** A C99 compound literal. The expression's type is taken from [ty]. *)
val compound : ty:ty -> init:init -> t

(** {1 Constant builders}

    Convenience wrappers around [const].
*)

(** An integer literal. *)
val int_ :
  ?suffix:[`u | `l | `ul | `ll | `ull] ->
  Cgen_utils.Bv.t ->
  ty:ty ->
  t

(** A string literal. *)
val str : string -> ty:ty -> t

(** A character literal. *)
val char_ : char -> ty:ty -> t

(** A single-precision floating-point literal. *)
val float_ : Cgen_utils.Float32.t -> ty:ty -> t

(** A double-precision floating-point literal. *)
val double : float -> ty:ty -> t

(** {1 Smart constructors for lvalues} *)

(** A named object lvalue. *)
val lvar : string -> ty:ty -> tlval

(** Dereference of a pointer expression. *)
val lderef : t -> ty:ty -> tlval

(** Member access producing an lvalue. *)
val lmember : lval:tlval -> field:string -> ty:ty -> tlval

(** Array indexing producing an lvalue. *)
val lindex : lval:tlval -> index:t -> ty:ty -> tlval

(** {1 Smart constructors for initializers} *)

(** A single-expression initializer. *)
val isingle : t -> init

(** A positional list of element initializers. *)
val iarray : init list -> init

(** A list of field-name/initializer pairs. *)
val istruct : (string * init) list -> init

(** A union initializer. *)
val iunion : name:string -> init:init -> init

(** {1 Operator precedence and associativity} *)

(** Precedence of a binary operator (delegates to {!Expr.prec_bop}). *)
val prec_bop : bop -> int

(** Associativity of a binary operator. *)
val assoc_bop : bop -> Expr.assoc

(** Precedence of a unary operator. *)
val prec_uop : uop -> int

(** Precedence of an expression node. *)
val prec_node : node -> int

(** Precedence of an expression. *)
val prec : t -> int

(** {1 Operator symbols} *)

(** Textual symbol of a binary operator. *)
val bop_symbol : bop -> string

(** Textual symbol of a unary operator. *)
val uop_symbol : uop -> string

(** {1 Pretty printers} *)

(** Renders an lvalue in C syntax. *)
val pp_lval : Format.formatter -> tlval -> unit

(** Renders an initializer in C syntax. Structure and union forms
    use C99 designated form ([.field = value]). *)
val pp_init : Format.formatter -> init -> unit

(** Renders an expression in C syntax, inserting parentheses only
    where required for correct binding. *)
val pp : Format.formatter -> t -> unit

(** Renders an expression as the operand of a postfix operator (a call
    callee, an index base), parenthesizing operands looser than a
    postfix expression (casts, unary and binary operators). *)
val pp_postfix : Format.formatter -> t -> unit

(** [to_string e] is [pp] rendered to a string. *)
val to_string : t -> string
