(** Untyped expressions.

    Parameterized over an annotation type ['a] in the
    "Trees That Grow" style: a parser supplies [Location.t],
    while hand-written ASTs can supply [unit].

    The polymorphic-variant hierarchies for operators are factored
    so that pure subsets ([bpure], [upure]) can be referenced
    directly by the typed AST, which forbids side-effecting
    operators in expression position.
*)

(** {1 Binary operators} *)

(** Arithmetic operators. [`mod_] denotes the [%] operator. *)
type barith = [
  | `add
  | `sub
  | `mul
  | `div
  | `mod_
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Short-circuiting logical operators ([&&], [||]). *)
type blogical = [
  | `land_
  | `lor_
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Bitwise operators. *)
type bbitwise = [
  | `and_
  | `or_
  | `xor
  | `shl
  | `shr
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Equality operators ([==], [!=]). *)
type eq = [
  | `eq
  | `ne
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Relational operators ([<], [>], [<=], [>=]). *)
type rel = [
  | `lt
  | `gt
  | `le
  | `ge
] [@@deriving bin_io, compare, equal, hash, sexp]

(** All comparison operators: equality and relational. *)
type cmp = [
  | eq
  | rel
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Assignment operators. [`assign] is plain [=]; the compound forms
    carry their underlying arithmetic or bitwise operator. *)
type bassign = [
  | `assign
  | `assign_arith of barith
  | `assign_bitwise of bbitwise
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pure (side-effect-free) binary operators. *)
type bpure = [
  | barith
  | blogical
  | bbitwise
  | cmp
] [@@deriving bin_io, compare, equal, hash, sexp]

(** All binary operators, pure or assigning. *)
type bop = [
  | bpure
  | bassign
] [@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Unary operators} *)

(** Arithmetic unary operators ([+], [-]). *)
type uarith = [
  | `minus
  | `plus
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Bitwise complement ([~]). *)
type ubitwise = [
  | `not_
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Logical negation ([!]). *)
type ulogical = [
  | `lnot_
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Memory-addressing unary operators: dereference ([*]) and
    address-of ([&]). *)
type umem = [
  | `deref
  | `addr
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Increment forms ([++x], [x++]). *)
type inc = [
  | `preinc
  | `postinc
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Decrement forms ([--x], [x--]). *)
type dec = [
  | `predec
  | `postdec
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Side-effecting unary operators: increment and decrement. *)
type uassign = [
  | inc
  | dec
] [@@deriving bin_io, compare, equal, hash, sexp]

(** Pure (side-effect-free) unary operators. *)
type upure = [
  | uarith
  | ubitwise
  | ulogical
  | umem
] [@@deriving bin_io, compare, equal, hash, sexp]

(** All unary operators, pure or assigning. *)
type uop = [
  | upure
  | uassign
] [@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Constants} *)

(** A literal constant. *)
type const =
  | Cint of {
      value  : Cgen_utils.Bv.t;
      suffix : [`u | `l | `ul | `ll | `ull] option;
      (** The integer-suffix as written, if any. The suffix narrows
          the inferred type per C99 §6.4.4.1. *)
      base : [`dec | `oct | `hex | `bin];
      (** The radix as written. A decimal constant's candidate types are
          signed; an octal, hexadecimal, or binary constant also admits the
          unsigned variant of each rank (C99 §6.4.4.1 ¶5; binary literals
          are a GCC/Clang extension, standard since C23). *)
    } (** An integer literal. *)
  | Cstr of string
  (** A string literal. *)
  | Cchar of char
  (** A character literal. *)
  | Cfloat of Cgen_utils.Float32.t
  (** A single-precision floating-point literal (suffix [f] or [F]). *)
  | Cdouble of float
  (** A double-precision floating-point literal. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Expressions} *)

(** An expression node paired with its annotation. *)
type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Econst of const
  (** A literal constant. *)
  | Ename of string
  (** A reference to a named identifier. The kind of entity the
      name refers to (e.g. a variable, function, enum constant,
      typedef) is determined during elaboration. *)
  | Elabaddr of string
  (** The address of a label (GNU [&&label]), which is a [void *] usable only
      as the operand of a computed [goto *]. *)
  | Eunary of {
      op  : uop;
      arg : 'a t;
    } (** A unary-operator application. *)
  | Ebinary of {
      op  : bop;
      lhs : 'a t;
      rhs : 'a t;
    } (** A binary-operator application. *)
  | Eindex of {
      arr : 'a t;
      idx : 'a t;
    } (** Array subscripting ([arr[idx]]). *)
  | Emember of {
      obj   : 'a t;
      field : string;
    } (** Direct member access ([obj.field]). *)
  | Earrow of {
      obj   : 'a t;
      field : string;
    } (** Indirect member access ([obj->field]). *)
  | Ecall of {
      callee : 'a t;
      args   : 'a t list;
    } (** A function call. *)
  | Ecast of {
      dst : 'a ty;
      arg : 'a t;
    } (** An explicit cast ([(dst)arg]). *)
  | Esizeof_e of 'a t
  (** [sizeof] applied to an expression. *)
  | Esizeof_t of 'a ty
  (** [sizeof] applied to a type name. *)
  | Econd of {
      cond  : 'a t;
      then_ : 'a t;
      else_ : 'a t;
    } (** The conditional operator ([cond ? then_ : else_]). *)
  | Ecomma of {
      lhs : 'a t;
      rhs : 'a t;
    } (** The comma operator: evaluate [lhs], discard, yield [rhs]. *)
  | Ecompound of {
      ty   : 'a ty;
      init : 'a init;
    } (** A C99 compound literal ([(ty){init}]). *)
  | Ebuiltin of {
      name : string;
      args : 'a builtin_arg list;
    } (** A compiler builtin call (e.g. [__builtin_va_arg]). [name] is
          the full builtin spelling. *)

(** A type expression. C array types embed a size expression, so
    [Type.t] is parameterized by the expression representation. *)
and 'a ty = 'a t Type.t

and 'a init =
  | Isingle of 'a t
  (** A single-expression initializer. *)
  | Icompound of ('a designator list * 'a init) list
  (** A brace-enclosed initializer list. Each element is paired
      with an optional sequence of designators: an empty list
      denotes positional initialization. *)

and 'a designator =
  | Dfield of string
  (** A field designator ([.field]). *)
  | Dindex of 'a t
  (** An array-index designator ([[i]]). *)

and 'a builtin_arg =
  | BAexpr of 'a t
  (** An ordinary expression argument. *)
  | BAtype of 'a ty
  (** A type-name argument, as in [__builtin_va_arg(ap, int)]. *)
[@@deriving bin_io, compare, equal, hash, sexp]

(** {1 Smart constructors} *)

(** A literal constant. *)
val const : const -> ann:'a -> 'a t

(** A reference to a named identifier. *)
val name : string -> ann:'a -> 'a t

(** The address of a label (GNU [&&label]). *)
val labaddr : string -> ann:'a -> 'a t

(** [sizeof] of an expression. *)
val sizeof_e : 'a t -> ann:'a -> 'a t

(** [sizeof] of a type name. *)
val sizeof_t : 'a ty -> ann:'a -> 'a t

(** A unary-operator application. *)
val unary : op:uop -> arg:'a t -> ann:'a -> 'a t

(** A binary-operator application. *)
val binary : op:bop -> lhs:'a t -> rhs:'a t -> ann:'a -> 'a t

(** Array subscripting ([arr[idx]]). *)
val index : arr:'a t -> idx:'a t -> ann:'a -> 'a t

(** Direct member access ([obj.field]). *)
val member : obj:'a t -> field:string -> ann:'a -> 'a t

(** Indirect member access ([obj->field]). *)
val arrow : obj:'a t -> field:string -> ann:'a -> 'a t

(** A function call. *)
val call : callee:'a t -> args:'a t list -> ann:'a -> 'a t

(** An explicit cast ([(dst)arg]). *)
val cast : dst:'a ty -> arg:'a t -> ann:'a -> 'a t

(** The conditional operator ([cond ? then_ : else_]). *)
val cond : cond:'a t -> then_:'a t -> else_:'a t -> ann:'a -> 'a t

(** The comma operator. *)
val comma : lhs:'a t -> rhs:'a t -> ann:'a -> 'a t

(** A C99 compound literal ([(ty){init}]). *)
val compound : ty:'a ty -> init:'a init -> ann:'a -> 'a t

(** A compiler builtin call. *)
val builtin : name:string -> args:'a builtin_arg list -> ann:'a -> 'a t

(** {1 Constant builders}

    Convenience wrappers around [const].
*)

(** An integer literal with an optional suffix and radix (default
    decimal). *)
val int_ :
  ?suffix:[`u | `l | `ul | `ll | `ull] ->
  ?base:[`dec | `oct | `hex | `bin] ->
  Cgen_utils.Bv.t ->
  ann:'a ->
  'a t

(** A string literal. *)
val str : string -> ann:'a -> 'a t

(** A character literal. *)
val char_ : char -> ann:'a -> 'a t

(** A single-precision floating-point literal. *)
val float_ : Cgen_utils.Float32.t -> ann:'a -> 'a t

(** A double-precision floating-point literal. *)
val double : float -> ann:'a -> 'a t

(** {1 Operator precedence and associativity}

    Useful for pretty printing, diagnostics, and any pass that needs
    to reason about operator binding without re-deriving the C
    precedence table.
*)

(** Operator associativity.

    C has no truly non-associative operators at the grammar level.
    Relational operators are formally left-associative even though
    chaining them is semantically unusual.
*)
type assoc = Aleft | Aright

(** Precedence of a binary operator.

    Lower values bind more tightly, matching the conventional C precedence table:
    - 3 = multiplicative
    - 4 = additive
    - ...
    - 14 = assignment
*)
val prec_bop : bop -> int

(** Associativity of a binary operator.

    Assignments are right-associative; all others are left-associative.
*)
val assoc_bop : bop -> assoc

(** Precedence of a unary operator.

    Postfix increment and decrement are at level 1. All other unaries are
    at level 2 (prefix).
*)
val prec_uop : uop -> int

(** True iff the unary operator appears after its operand (postfix [++]/[--]). *)
val uop_is_postfix : uop -> bool

(** Precedence of an expression node.

    - Atoms (constants, names) are at level 0
    - Postfix forms at 1
    - Prefix forms at 2
    - Ternary at 13
    - Comma at 15
*)
val prec_node : _ node -> int

(** Precedence of an expression. *)
val prec : _ t -> int

(** {1 Operator symbols} *)

(** Textual symbol of a binary operator. *)
val bop_symbol : bop -> string

(** Textual symbol of a unary operator. *)
val uop_symbol : uop -> string

(** {1 Pretty printers} *)

(** Renders a literal constant in C syntax. *)
val pp_const : Format.formatter -> const -> unit

(** Renders an initializer designator ([.field] or [[i]]). *)
val pp_designator : Format.formatter -> 'a designator -> unit

(** Renders an initializer (either a single expression or a brace-
    enclosed list with optional designators). *)
val pp_init : Format.formatter -> 'a init -> unit

(** Renders an expression in C syntax, inserting parentheses only
    where required for correct binding. *)
val pp : Format.formatter -> 'a t -> unit

(** [to_string e] is [pp] rendered to a string. *)
val to_string : 'a t -> string
