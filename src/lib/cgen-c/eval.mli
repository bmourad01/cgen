(** Constant-expression evaluation for the C frontend.

    Implements the semantics required by C99 §6.6 (constant
    expressions). Operates on typechecked expressions ([Texpr.t]).
    The elaborator calls these entry points wherever the standard
    requires a constant.

    The three constant-expression categories of §6.6 form a lattice:

    {v
        ice <: arith <: init
    v}

    encoded directly in the types so that, e.g., an [ice] context can
    only produce a [Vint], and a [Vstring] is constructible only at
    rows containing [`init].

    - [ice]:   integer constant expressions (§6.6 ¶6).
    - [arith]: arithmetic constant expressions (§6.6 ¶8). Adds
               floating-point constants.
    - [init]:  constant expressions in initializers (§6.6 ¶7). Adds
               string literals and address constants.
*)

open Core

(** {1 Mode tags}

    Row-typed polymorphic variants give built-in subtyping.
*)

type ice = [`ice]
type arith = [ice | `arith]
type init = [arith | `init]

(** {1 Values}

    A reduced constant value. Each constructor declares the minimum
    row at which it is constructible; pattern matching against a
    concrete row eliminates the unreachable branches at compile time.
*)
type _ value =
  | Vint : Cgen_utils.Bv.t -> [> ice] value
  (** An integer or character constant, masked to its type's width. *)
  | Vfloat : Cgen_utils.Float32.t -> [> arith] value
  (** A single-precision floating-point constant. *)
  | Vdouble : float -> [> arith] value
  (** A double-precision floating-point constant. *)
  | Vaddr : {
      sym : string;
      off : Cgen_utils.Bv.t;
    } -> [> init] value
  (** A symbol plus a byte offset (§6.6 ¶9). *)
  | Vstring : string -> [> init] value
  (** A string literal. *)
  | Vnull : [> init] value
  (** A null pointer constant (§6.3.2.3 ¶3). *)
[@@deriving sexp_of]

(** {1 Evaluator context}

    Parameterized by the same row tag as [value], so a context can
    only be used to produce values it is permitted to produce.
*)
type 'm t

val create_ice   : Layout.t -> ice   t
val create_arith : Layout.t -> arith t
val create_init  : Layout.t -> init  t

(** {1 Equality on values}

    Heterogeneous: the two values may carry different row tags.

    Two values are equal iff they have the same constructor and
    equal payloads.
*)
val equal_value : 'a value -> 'b value -> bool

(** {1 Folding} *)

(** [fold t e] folds constant subexpressions of [e] in place.

    The returned [Texpr.t] may still contain non-constant subterms,
    so this function does not error on non-constant inputs.

    Errors are surfaced for the constraint violations the standard
    treats as ill-formed in a constant-expression context, such as:
    - signed overflow
    - division or modulo by zero
    - out-of-range shift counts
    - out-of-range float-to-integer conversions.
*)
val fold : _ t -> Texpr.t -> Texpr.t Or_error.t

(** {1 Reducing to a value} *)

(** [int_const t e] is [fold t e] followed by a check that the result
    is an integer literal.

    Available at any mode.
*)
val int_const : _ t -> Texpr.t -> Cgen_utils.Bv.t Or_error.t

(** [const t e] is [fold t e] followed by a projection into the value
    space.

    The result row matches the context:
    - an [ice t] only produces [Vint]
    - an [arith t] additionally produces [Vfloat]/[Vdouble]
    - an [init t] further produces [Vaddr], [Vstring], and [Vnull].
*)
val const : 'm t -> Texpr.t -> 'm value Or_error.t
