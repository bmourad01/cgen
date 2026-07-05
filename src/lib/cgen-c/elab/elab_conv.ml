(* C99 conversion rules. *)

open Core

module Bv = Cgen_utils.Bv
module E = Cgen_utils.Monads.Error
module ET = Elab_type
module DM = Data_model

let pnorm f tenv ty = f @@ ET.normalize tenv ty

let is_void       = pnorm Type.is_void
let is_array      = pnorm Type.is_array
let is_function   = pnorm Type.is_function
let is_pointer    = pnorm Type.is_pointer
let is_integer    = pnorm Type.is_integer
let is_floating   = pnorm Type.is_floating
let is_arithmetic = pnorm Type.is_arithmetic
let is_scalar     = pnorm Type.is_scalar

let int_bits dm tenv ty = match ET.normalize tenv ty with
  | Tbase {base = Bbool; _}              -> Some DM.bool_bits
  | Tbase {base = Bchar; _}              -> Some DM.char_bits
  | Tbase {base = Bint (Ichar _); _}     -> Some DM.char_bits
  | Tbase {base = Bint (Ishort _); _}    -> Some DM.short_bits
  | Tbase {base = Bint (Iint _); _}      -> Some (DM.int_bits dm)
  | Tbase {base = Bint (Ilong _); _}     -> Some (DM.long_bits dm)
  | Tbase {base = Bint (Ilonglong _); _} -> Some DM.long_long_bits
  | Tnamed {kind = `enum; _}             -> Some (DM.int_bits dm)
  | _ -> None

let int_sign dm tenv ty : Type.sign option =
  match ET.normalize tenv ty with
  | Tbase {base = Bbool; _} -> Some Sunsigned
  | Tbase {base = Bchar; _} when DM.char_signed dm -> Some Ssigned
  | Tbase {base = Bchar; _} -> Some Sunsigned
  | Tbase {base = Bint i; _} -> Some (Type.ity_sign i)
  | Tnamed {kind = `enum; _} -> Some Ssigned
  | _ -> None

(* Lvalue-to-rvalue conversion (§6.3.2.1 ¶2)

   An lvalue (that is not an array) is converted to the value stored
   at the designated location; the result type has the lvalue's type
   with cv-qualifiers stripped from the outer level.

   This function does not decay arrays or functions. Instead, those
   are distinct conversions via `decay_array` and `decay_function`.
*)
let rec to_rvalue tenv (lv : Texpr.tlval) =
  let ty = Type.unqualified lv.ty in
  match lv.node with
  | Lvar name -> Texpr.var name ~ty
  | Lderef arg -> Texpr.unary ~op:`deref ~arg ~ty
  | Lmember {lval; field} ->
    let obj = to_rvalue tenv lval in
    Texpr.member ~obj ~field ~ty
  | Lindex {lval; index} ->
    let arr = decay_array tenv @@ to_rvalue tenv lval in
    Texpr.index ~arr ~idx:index ~ty

(* Array-to-pointer decay (§6.3.2.1 ¶3)

   An expression of array type is converted to a pointer to the
   array's first element. We express the decay as an explicit
   cast from the array type to the pointer-to-element type.
*)
and decay_array tenv (e : Texpr.t) =
  match ET.normalize tenv e.ty with
  | Tarray {elem; _} -> Texpr.cast ~dst:(Type.ptr elem) ~arg:e
  | _ -> e

(* Function-to-pointer decay (§6.3.2.1 ¶4)

   A function designator is converted to a pointer-to-function.
*)
let decay_function tenv (e : Texpr.t) =
  match ET.normalize tenv e.ty with
  | Tfun _ -> Texpr.cast ~dst:(Type.ptr e.ty) ~arg:e
  | _ -> e

(* All-in-one: l-to-r then array/function decay.

   This is the common case when consuming a value in an rvalue context.
*)
let lvalue_to_rvalue tenv (lv : Texpr.tlval) : Texpr.t =
  to_rvalue tenv lv |> decay_array tenv |> decay_function tenv

(* Integer promotion (§6.3.1.1 ¶2)

   An operand of type:
   - `_Bool`
   - `char`
   - `signed char`
   - `unsigned char`
   - `short`
   - `unsigned short`
     or an integer type whose width is less than that of `int`, is
     converted to `int` (`signed` if `int` can hold all values,
     otherwise `unsigned int`).

   For standard data models, `int` is always wide enough, so we
   always promote to signed `int`.
*)
let promote_integer dm tenv (e : Texpr.t) : Texpr.t =
  match int_bits dm tenv e.ty with
  | Some bits when bits < DM.int_bits dm ->
    let dst = Type.int_ () in
    Texpr.cast ~dst ~arg:e
  | _ -> e

(* Usual arithmetic conversions (§6.3.1.8)

   Given two operands of arithmetic types, convert both to a common
   type. Returns the converted operands. Caller passes the operands
   and gets back the converted pair plus the resulting common type
   (which is also each operand's new type).

   Order (after integer promotion):
   1. If either operand is `double`, both become `double`.
   2. If either operand is `float`, both become `float`.
   3. Otherwise, apply integer rules: widen to the wider type;
      on same-width `signed`/`unsigned` mix, prefer `unsigned`.
*)
let usual_arith_conv dm tenv (a : Texpr.t) (b : Texpr.t) =
  let na = ET.normalize tenv a.ty in
  let nb = ET.normalize tenv b.ty in
  let cast_to dst e =
    if Type.equal Texpr.equal e.Texpr.ty dst then e
    else Texpr.cast ~dst ~arg:e in
  let either_is base_ty =
    Type.equal Texpr.equal na base_ty ||
    Type.equal Texpr.equal nb base_ty in
  (* Floating cases first. *)
  let f64 = Type.double_ () in
  let f32 = Type.float_ () in
  if either_is f64 then
    cast_to f64 a, cast_to f64 b, f64
  else if either_is f32 then
    cast_to f32 a, cast_to f32 b, f32
  else
    (* Integer case: promote, then pick the wider type. *)
    let a = promote_integer dm tenv a in
    let b = promote_integer dm tenv b in
    let na = ET.normalize tenv a.ty in
    let nb = ET.normalize tenv b.ty in
    let bits_of t = Option.value (int_bits dm tenv t) ~default:0 in
    let sign_of t = Option.value (int_sign dm tenv t) ~default:Type.Ssigned in
    let wa = bits_of na in
    let wb = bits_of nb in
    let dst =
      if wa > wb then na
      else if wb > wa then nb
      (* Same width; pick whichever side is unsigned. *)
      else match sign_of na, sign_of nb with
        | Sunsigned, _ -> Type.unqualified na
        | _, Sunsigned -> Type.unqualified nb
        | _ -> Type.unqualified na in
    cast_to dst a, cast_to dst b, dst

(* Default argument promotions (§6.5.2.2 ¶6, ¶7)

   Applied to arguments in:
   - variadic positions of a prototyped function (after the named
     parameters)
   - all arguments of a non-prototyped function.

   Rules:
   - integer promotions
   - `float` arguments promote to `double`
*)
let default_arg_promote dm tenv e =
  let e = promote_integer dm tenv e in
  match ET.normalize tenv e.ty with
  | Tbase {base = Bfloat Ffloat; _} ->
    let dst = Type.double_ () in
    Texpr.cast ~dst ~arg:e
  | _ -> e

(* §6.3.2.3 ¶3: a null pointer constant is an integer constant
   expression evaluating to zero, optionally cast to `void *`.

   Defer to the constant evaluator: at the `init` row it returns
   `Vnull` for the pointer-typed forms, and `Vint 0` for bare
   integer constant expressions whose value is zero.
*)
let is_null_pointer_constant eval e =
  match Eval.const eval e with
  | Ok Vnull -> true
  | Ok (Vint v) -> Bv.(v = zero)
  | _ -> false

let is_cv_subset a b = Type.Cv.equal (Type.Cv.combine a b) b

(* Default argument promotion at the type level (§6.5.2.2 ¶6, ¶7).

   - `_Bool`, `char`, `short`, and their signed/unsigned variants
     promote to `int`
   - `float` promotes to `double`

   Everything else passes through. Used for K&R/prototype compatibility
   below. On the expression level the corresponding cast is performed by
   `default_arg_promote`.
*)
let default_arg_promote_ty tenv ty =
  match ET.normalize tenv ty with
  | Tbase {base = Bbool; _}
  | Tbase {base = Bchar; _}
  | Tbase {base = Bint (Ichar _); _}
  | Tbase {base = Bint (Ishort _); _}
    -> Type.int_ ()
  | Tbase {base = Bfloat Ffloat; _}
    -> Type.double_ ()
  | _ -> ty

(* Type compatibility, per §6.2.7 and §6.7.5.1.

   Two qualified types are compatible iff their qualifiers match and
   their unqualified versions are compatible (§6.7.3 ¶10), so at each
   layer we compare `cv_of` first and then descend on the unqualified
   forms.

   Structurally:
   - Two base types: same `base` tag.
   - Two pointer types: matching `restrict` and compatible pointees.
   - Two array types: compatible elements and, per §6.7.5.2 ¶6,
     either at least one size missing (incomplete array implies
     compatiblity with any size), or both ICEs with equal value, or
     at least one non-ICE (compatible at compile time; a runtime
     mismatch is UB). Equality of ICE sizes is by *value*, via
     `Eval.int_const`, so syntactically distinct forms like `3` and
     `1+2` compare equal.
   - Two function types (§6.7.5.3 ¶15): always require compatible
     result types. Then:
       * Both prototyped (`params = Some _`): same `variadic` and
         elementwise compatible parameter lists.
       * Both K&R (`params = None`): trivially compatible.
       * One prototyped, one K&R: the prototype must not be variadic
         and each of its parameter types must already be in
         default-argument-promoted form. Parameter counts are not
         compared because the K&R side carries no count information.
     Parameter names are irrelevant throughout.
   - Two named types (struct/union/enum tags after normalize): same
     kind and same tag name.
*)
let rec compatible tenv eval a b =
  let a = ET.normalize tenv a in
  let b = ET.normalize tenv b in
  Type.Cv.equal (Type.cv_of a) (Type.cv_of b) &&
  compatible_unqual tenv eval (Type.unqualified a) (Type.unqualified b)

and compatible_unqual tenv eval a b = match a, b with
  | Tbase {base = ba; _}, Tbase {base = bb; _} ->
    Type.equal_base ba bb
  | Tptr {pointee = pa; restrict = ra; _},
    Tptr {pointee = pb; restrict = rb; _} ->
    Bool.(ra = rb) && compatible tenv eval pa pb
  | Tarray {elem = ea; size = sa; _},
    Tarray {elem = eb; size = sb; _} ->
    compatible tenv eval ea eb && compatible_sizes eval sa sb
  | Tfun {result = ra; params = pa; variadic = va},
    Tfun {result = rb; params = pb; variadic = vb} ->
    compatible tenv eval ra rb &&
    begin match pa, pb with
      | None, None -> true
      | Some pl, Some pr ->
        Bool.(va = vb) &&
        List.equal (compatible_param tenv eval) pl pr
      | Some ps, None -> not va && compatible_proto_kr tenv eval ps
      | None, Some ps -> not vb && compatible_proto_kr tenv eval ps
    end
  | Tnamed {kind = ka; name = na; _},
    Tnamed {kind = kb; name = nb; _} ->
    Type.equal_named ka kb && String.(na = nb)
  | _ -> false

and compatible_sizes eval sa sb = match sa, sb with
  | None, _ | _, None -> true
  | Some xa, Some xb ->
    match Eval.(int_const eval xa, int_const eval xb) with
    | Ok va, Ok vb -> Bv.(va = vb)
    | _ -> true

and compatible_param tenv eval a b =
  compatible tenv eval a.Type.ptype b.Type.ptype

and compatible_param_promote tenv eval a =
  compatible tenv eval a.Type.ptype @@
  default_arg_promote_ty tenv a.Type.ptype

(* §6.7.5.3 ¶15: one type prototyped, the other a K&R declarator.

   The prototype must not be variadic and each of its parameter
   types must be unchanged by the default argument promotions.
*)
and compatible_proto_kr tenv eval ps =
  List.for_all ps ~f:(compatible_param_promote tenv eval)

(* Pointee compatibility for the assignment-conversion rule.

   §6.5.16.1 ¶1 calls for "pointers to qualified or unqualified
   versions of compatible types". The outer cv-qualifier on each
   pointee is checked separately by `is_cv_subset` in
   `convert_for_assign`, so here we strip it before delegating to
   `compatible`.
*)
let pointee_compatible tenv eval a b =
  compatible tenv eval (Type.unqualified a) (Type.unqualified b)

(* Assignment conversion (§6.5.16.1 ¶1).

   Cases:
   - Equal after normalization: identity.
   - Both arithmetic: cast to LHS.
   - LHS pointer, RHS null pointer constant: cast to LHS.
   - Both pointer:
       * LHS pointee must carry all of RHS pointee's qualifiers.
       * Then either: one side is [void *] and the other an
         object-pointer (function pointers are excluded), or the
         pointees are compatible at the outer level.
   - LHS `_Bool`, RHS pointer: truth-value conversion. Not yet
     implemented.
*)
let convert_for_assign tenv eval ~lhs ~(rhs : Texpr.t) =
  let dst = Type.unqualified lhs in
  let nl = ET.normalize tenv dst in
  let nr = ET.normalize tenv rhs.ty in
  let pp = Type.pp_with Texpr.pp in
  match nl, nr with
  | _ when Type.equal Texpr.equal nl nr -> Ok (rhs, None)
  (* Both arithmetic (§6.5.16.1): includes enum types, which are integer
     types (§6.7.2.2) freely convertible to and from other arithmetic types. *)
  | _ when Type.is_arithmetic nl && Type.is_arithmetic nr ->
    Ok (Texpr.cast ~dst ~arg:rhs, None)
  | Tptr _, _ when is_null_pointer_constant eval rhs ->
    Ok (Texpr.cast ~dst ~arg:rhs, None)
  | Tptr {pointee = lp; _}, Tptr {pointee = rp; _} ->
    if not (is_cv_subset (Type.cv_of rp) (Type.cv_of lp)) then
      E.failf
        "assignment discards qualifiers from pointer target: '%a' to '%a'"
        pp nr pp nl ()
    else
      let nlp = ET.normalize tenv lp in
      let nrp = ET.normalize tenv rp in
      let l_void = Type.is_void nlp in
      let r_void = Type.is_void nrp in
      let l_fun = Type.is_function nlp in
      let r_fun = Type.is_function nrp in
      (* `void *` interoperates with any object-pointer type, but
         not with function pointers. *)
      if (l_void && not r_fun) || (r_void && not l_fun) then
        Ok (Texpr.cast ~dst ~arg:rhs, None)
      else if pointee_compatible tenv eval lp rp then
        Ok (Texpr.cast ~dst ~arg:rhs, None)
      else
        (* The compatible-pointee case above is conformant with §6.5.16.1.
           gcc, however, accepts assignment between distinct, non-compatible
           object-pointer types (differing nested qualifiers or signedness)
           with a warning rather than an error; we match that leniency and
           attach a diagnostic. The qualifier-discard check above still rejects
           dropping a top-level `const`/`volatile`. *)
        let w =
          Format.asprintf
            "assignment from incompatible pointer type: '%a' to '%a'"
            pp nr pp nl in
        Ok (Texpr.cast ~dst ~arg:rhs, Some w)
  | _ ->
    E.failf
      "assignment from incompatible types: '%a' to '%a'"
      pp nr pp nl ()

(* Return conversion (§6.8.6.4 ¶3): same constraints as assignment. *)
let convert_for_return tenv eval ~ret ~rhs =
  convert_for_assign tenv eval ~lhs:ret ~rhs
