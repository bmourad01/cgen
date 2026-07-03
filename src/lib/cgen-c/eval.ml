(* Constant-expression evaluation for the C frontend.

   This module implements the semantics required by C99 §6.6:

   - [ice]:   integer constant expressions (§6.6 ¶6)
   - [arith]: arithmetic constant expressions (§6.6 ¶8)
   - [init]:  constant expressions in initializers (§6.6 ¶7)

   The three modes form a row-typed lattice `ice <: arith <: init`.
   The context `t` and result `value` are both parameterized by the
   row, so the type system enforces that, e.g., an `ice` context can
   only produce a `Vint`.

   The folder `fold` is mode-agnostic: it folds whatever it can.
   The mode is only consulted by `const` when classifying the folded
   result.

   Constraint violations that §6.5/§6.6 flag as undefined or out of
   range in a constant-expression context (signed overflow, division
   by zero, out-of-range shift counts, out-of-range float-to-integer
   conversions) are surfaced as errors rather than silently wrapped.
   In this case, §6.6 ¶4 says "Each constant expression shall evaluate
   to a constant that is in the range of representable values for its
   type."
*)

open Core
open Monads.Std

module E = Monad.Result.Error
module O = Monad.Option
module Bv = Cgen.Bv
module D = Data_model
module TE = Type_env
module F32 = Cgen_utils.Float32

(* Mode rows. *)
type ice   = [`ice]
type arith = [ice | `arith]
type init  = [arith | `init]

(* GADT witness for the row carried by a context. *)
type _ mode_tag =
  | Ice   : ice   mode_tag
  | Arith : arith mode_tag
  | Init  : init  mode_tag

(* The result of constant folding.

   Each constructor declares the minimum row at which it is
   constructible, so the API can return a value whose row matches
   the context.
*)
type _ value =
  | Vint : Bv.t -> [> ice] value
  | Vfloat : F32.t -> [> arith] value
  | Vdouble : float -> [> arith] value
  | Vaddr : {
      sym : string;
      off : Bv.t;
    } -> [> init] value
  | Vstring : string -> [> init] value
  | Vnull : [> init] value
[@@deriving sexp_of]

type 'm t = {
  dm     : D.t;
  layout : Layout.t;
  tenv   : TE.t;
  mode   : 'm mode_tag;
}

let create_ice layout = {
  dm = Layout.dmodel layout;
  layout;
  tenv = Layout.tenv layout;
  mode = Ice;
}

let create_arith layout = {
  dm = Layout.dmodel layout;
  layout;
  tenv = Layout.tenv layout;
  mode = Arith;
}

let create_init layout = {
  dm = Layout.dmodel layout;
  layout;
  tenv = Layout.tenv layout;
  mode = Init;
}

(* Heterogeneous structural equality.

   Two values are equal iff they have the same constructor and equal
   payloads, regardless of which row tags the arguments carry.
*)
let equal_value : type a b. a value -> b value -> bool = fun x y ->
  match x, y with
  | Vint a, Vint b -> Bv.equal a b
  | Vfloat a, Vfloat b -> F32.equal a b
  | Vdouble a, Vdouble b -> Float.equal a b
  | Vaddr a, Vaddr b -> String.equal a.sym b.sym && Bv.equal a.off b.off
  | Vstring a, Vstring b -> String.equal a b
  | Vnull, Vnull -> true
  | (Vint _ | Vfloat _ | Vdouble _ | Vaddr _ | Vstring _ | Vnull), _ ->
    false

(* Integer type metadata (§6.2.5, §6.7.2.2) *)

(* §6.2.5 ¶15: the signedness of plain `char` is implementation-defined.

   For us, this is reflected in `Data_model`.
*)
let plain_char_sign dm : Type.sign =
  if D.char_signed dm then Ssigned else Sunsigned

(* §6.2.5: integer base types and their widths under the current
   data model. *)
let int_info_base dm : Type.base -> (int * Type.sign) option = function
  | Bbool              -> Some (D.bool_bits, Sunsigned)
  | Bchar              -> Some (D.char_bits, plain_char_sign dm)
  | Bint Ichar s       -> Some (D.char_bits, s)
  | Bint Ishort s      -> Some (D.short_bits, s)
  | Bint Iint s        -> Some (D.int_bits dm, s)
  | Bint Ilong s       -> Some (D.long_bits dm, s)
  | Bint Ilonglong s   -> Some (D.long_long_bits, s)
  | Bvoid | Bfloat _   -> None

(* §6.7.2.2 ¶4 makes the underlying integer type of an [enum]
   implementation-defined. We choose `signed int` here.

   §6.4.4.3 ¶2 independently fixes the type of an enumeration constant
   to `int`, so this matches the constant-use case.

   Larger enums would need a wider underlying type, which we do not yet
   support.
*)
let int_info t (ty : Texpr.ty) = match ty with
  | Tbase {base; _} ->
    int_info_base t.dm base
  | Tnamed {kind = `enum; _} ->
    Some (D.int_bits t.dm, Type.Ssigned)
  | _ -> None

let float_kind (ty : Texpr.ty) = match ty with
  | Tbase {base = Bfloat Ffloat; _}  -> Some `f32
  | Tbase {base = Bfloat Fdouble; _} -> Some `f64
  | _ -> None

(* Bit-pattern helpers *)

let mask bits bv = Bv.extract ~hi:(bits - 1) ~lo:0 bv

(* §6.2.6.2: two's-complement encoding.

   Interpret a `bits`-wide bit pattern as a signed mathematical value
   via `Z.t`.
*)
let to_signed_z ~bits v =
  let z = Bv.to_bigint v in
  let half = Z.shift_left Z.one (bits - 1) in
  if Z.lt z half then z else Z.sub z (Z.shift_left Z.one bits)

(* Convert a signed mathematical value (`Z.t`) back to a
   `bits`-wide bit pattern, erroring if it is outside the
   signed range.

   §6.5 ¶5: signed integer overflow has undefined behavior.
   §6.6 ¶4: a constant expression must evaluate to a value
            representable in its type.

   We therefore treat overflow as a constraint violation.
*)
let from_signed_z_checked ~bits z =
  let max_s = Z.pred (Z.shift_left Z.one (bits - 1)) in
  let min_s = Z.neg (Z.shift_left Z.one (bits - 1)) in
  if Z.gt z max_s || Z.lt z min_s then
    E.failf "signed integer overflow in constant expression" ()
  else
    let bp =
      if Z.geq z Z.zero then z
      else Z.add z (Z.shift_left Z.one bits) in
    Ok (Bv.bigint_unsafe bp)

(* `Texpr` builders and extractors *)

let mk_int ty value = Texpr.int_ value ~ty
let mk_bool ty b = mk_int ty (if b then Bv.one else Bv.zero)
let mk_f32 ty f = Texpr.float_ f ~ty
let mk_f64 ty d = Texpr.double d ~ty

let extract_int t (e : Texpr.t) = match e.node, int_info t e.ty with
  | Econst Cint {value; _}, Some (bits, _) ->
    Some (mask bits value)
  (* §6.4.4.4 ¶10: an integer character constant has type `int`;
     we mask to the type recorded on the Texpr. *)
  | Econst Cchar c, Some (bits, _) ->
    let ci = Char.to_int c in
    Some Bv.(int ci mod modulus bits)
  | _ -> None

let extract_f32 (e : Texpr.t) = match e.node with
  | Econst Cfloat f -> Some f
  | _ -> None

let extract_f64 (e : Texpr.t) = match e.node with
  | Econst Cdouble d -> Some d
  | _ -> None

(* §6.3.1.2 ¶1 / §6.8.4.1 / §6.5.13 ¶3: an expression is "true" in
   a control-flow context iff it compares unequal to zero. *)
let is_truthy bv = Bv.(bv <> zero)

(* Truthiness for any folded constant: integer, character, float,
   string, or address.

   Returns `None` if the truthiness cannot be determined from the
   (already-folded) expression.
*)
let is_truthy_expr t (e : Texpr.t) =
  match extract_int t e with
  | Some v -> Some (is_truthy v)
  | None -> match e.node with
    (* IEEE: NaN compares unequal to zero, hence truthy. *)
    | Econst Cfloat f  -> Some F32.(f <> of_float 0.0)
    | Econst Cdouble d -> Some Float.(d <> 0.0)
    (* §6.3.2.1 ¶3: a string literal decays to a non-null pointer. *)
    | Econst Cstr _ -> Some true
    (* §6.5.3.2 ¶3: the result of unary [&] is a pointer to its
       operand, which for an object designator is never null. *)
    | Eaddrof _ -> Some true
    | _ -> None

(* Integer cast (§6.3.1.3) *)

(* §6.3.1.3:

   - If the new type can represent the value, it is unchanged.
   - If the new type is unsigned, the value is reduced modulo 2^N.
   - If the new type is signed and the value does not fit, the
     result is implementation-defined; we adopt the conventional
     two's-complement wrap, obtained by masking.
*)
let cast_int ~src_bits ~(src_sign : Type.sign) ~dst_bits v =
  if dst_bits <= src_bits
  then mask dst_bits v
  else match src_sign with
    | Ssigned   -> Bv.sext v src_bits dst_bits
    | Sunsigned -> mask dst_bits v

(* Integer-float conversions (§6.3.1.4 / §6.3.1.5 / §6.3.1.6) *)

(* §6.3.1.4 ¶1 (float to integer): the fractional part is discarded
   (truncation toward zero); if the integral part cannot be
   represented in the destination type, the behavior is undefined
   (we error).

   NaN as a source is likewise undefined (result is an error).
*)
let f32_to_int ~bits ~(sign : Type.sign) f =
  if F32.is_nan f then
    E.failf
      "out-of-range NaN to integer conversion in constant \
       expression for %a %d bits" Type.pp_sign sign bits ()
  else
    let v_opt = match bits, sign with
      | 8,  Ssigned   -> Some Bv.(int   (F32.to_int8   f) mod modulus 8)
      | 16, Ssigned   -> Some Bv.(int   (F32.to_int16  f) mod modulus 16)
      | 32, Ssigned   -> Some Bv.(int32 (F32.to_int32  f) mod modulus 32)
      | 64, Ssigned   -> Some Bv.(int64 (F32.to_int64  f) mod modulus 64)
      | 8,  Sunsigned -> Some Bv.(int   (F32.to_uint8  f) mod modulus 8)
      | 16, Sunsigned -> Some Bv.(int   (F32.to_uint16 f) mod modulus 16)
      | 32, Sunsigned -> Some Bv.(int32 (F32.to_uint32 f) mod modulus 32)
      | 64, Sunsigned -> Some Bv.(int64 (F32.to_uint64 f) mod modulus 64)
      | _ -> None in
    match v_opt with
    | Some v -> Ok v
    | None ->
      E.failf
        "unsupported float-to-integer conversion width \
         for %a %d bits" Type.pp_sign sign bits ()

(* Same as above, but for `double`. *)
let f64_to_int ~bits ~sign d =
  if Float.is_nan d then
    E.failf
      "out-of-range NaN to integer conversion in constant \
       expression for %a %d bits" Type.pp_sign sign bits ()
  else
    let pow2 n = Float.(2.0 ** of_int n) in
    let in_signed_range b =
      let upper = pow2 (b - 1) in
      Float.(d >= neg upper) && Float.(d < upper) in
    let in_unsigned_range b =
      let upper = pow2 b in
      Float.(d >= 0.0) && Float.(d < upper) in
    let ok = match (sign : Type.sign) with
      | Ssigned   -> in_signed_range bits
      | Sunsigned -> in_unsigned_range bits in
    if not ok then
      E.failf
        "out-of-range float-to-integer conversion in constant \
         expression for %a %d bits" Type.pp_sign sign bits ()
    else
      let v_opt = match bits, (sign : Type.sign) with
        | (8 | 16 | 32), _ ->
          Some Bv.(int (Int.of_float d) mod modulus bits)
        | 64, Ssigned ->
          Some Bv.(int64 (Int64.of_float d) mod modulus 64)
        | 64, Sunsigned when Float.(d < pow2 63) ->
          Some Bv.(int64 (Int64.of_float d) mod modulus 64)
        | 64, Sunsigned ->
          (* Two-step conversion to avoid Int64 overflow at 2^63. *)
          let open Int64 in
          let halved = d /. 2.0 in
          let high = of_float halved in
          let two_high = high * 2L in
          let low = of_float (d -. to_float two_high) in
          let combined = two_high + low in
          Some Bv.(int64 combined mod modulus 64)
        | _ -> None in
      match v_opt with
      | Some v -> Ok v
      | None ->
        E.failf
          "unsupported float-to-integer conversion width \
           for %a %d bits" Type.pp_sign sign bits ()

(* §6.3.1.4 ¶2 / §6.3.1.7 (integer to float): if the value can be
   represented in the result type exactly, that is the result.

   Otherwise, it is rounded in an implementation-defined way (we
   defer to the underlying IEEE 754 rounding).
*)
let int_to_f32 ~bits ~sign v =
  match bits, (sign : Type.sign) with
  | 8,  Ssigned   -> Some (F32.of_int8   (Z.to_int (to_signed_z ~bits v)))
  | 16, Ssigned   -> Some (F32.of_int16  (Z.to_int (to_signed_z ~bits v)))
  | 32, Ssigned   -> Some (F32.of_int32  (Bv.to_int32 v))
  | 64, Ssigned   -> Some (F32.of_int64  (Bv.to_int64 v))
  | 8,  Sunsigned -> Some (F32.of_uint8  (Bv.to_int v))
  | 16, Sunsigned -> Some (F32.of_uint16 (Bv.to_int v))
  | 32, Sunsigned -> Some (F32.of_uint32 (Bv.to_int32 v))
  | 64, Sunsigned -> Some (F32.of_uint64 (Bv.to_int64 v))
  | _ -> None

(* Same as above, but for `double`. *)
let int_to_f64 ~bits ~sign v =
  match bits, (sign : Type.sign) with
  | (8 | 16 | 32), Ssigned ->
    Some (Float.of_int (Z.to_int (to_signed_z ~bits v)))
  | (8 | 16 | 32), Sunsigned ->
    Some (Float.of_int (Bv.to_int v))
  | 64, Ssigned ->
    Some (Int64.to_float (Bv.to_int64 v))
  | 64, Sunsigned ->
    let open Int64 in
    let i = Bv.to_int64 v in
    if i >= 0L then Some (to_float i) else
      (* High bit set: split the magnitude to dodge Int64 overflow. *)
      let half, low = i lsr 1, i land 1L in
      Some (2.0 *. to_float half +. to_float low)
  | _ -> None

(* Shift count check (§6.5.7 ¶3) *)

let shift_count0 ~lhs_bits b = match Bv.to_int b with
  | n when n >= 0 && n < lhs_bits -> Some n
  | _ -> None
  | exception _ -> None

let shift_count ~lhs_bits b = match shift_count0 ~lhs_bits b with
  | None -> E.failf "shift count out of range in constant expression" ()
  | Some n -> Ok n

(* Integer operators *)

(* §6.5.5–6 (multiplicative, additive). For signed operands the
   result must fit; otherwise §6.5 ¶5 declares UB and §6.6 ¶4
   forbids it in a constant expression. We catch this via
   `from_signed_z_checked`.

   For unsigned operands, §6.2.5 ¶9 mandates wrap modulo 2^N.
*)
let eval_iarith_unsigned ~bits (op : Expr.barith) a b =
  let m = Bv.modulus bits in
  match op with
  | `add -> Ok Bv.((a + b) mod m)
  | `sub -> Ok Bv.((a - b) mod m)
  | `mul -> Ok Bv.((a * b) mod m)
  | `div when Bv.(b = zero) ->
    E.failf "division by zero in constant expression" ()
  | `div -> Ok Bv.((a / b) mod m)
  | `mod_ when Bv.(b = zero) ->
    E.failf "modulo by zero in constant expression" ()
  | `mod_ -> Ok Bv.(rem a b mod m)

let eval_iarith_signed ~bits (op : Expr.barith) a b =
  let open E.Let in
  let sa = to_signed_z ~bits a in
  let sb = to_signed_z ~bits b in
  let z_result = match op with
    | `add -> Ok Z.(sa + sb)
    | `sub -> Ok Z.(sa - sb)
    | `mul -> Ok Z.(sa * sb)
    | `div when Z.(equal sb zero) ->
      E.failf "division by zero in constant expression" ()
    | `div -> Ok (Z.div sa sb) (* truncation toward zero per §6.5.5 ¶6 *)
    | `mod_ when Z.(equal sb zero) ->
      E.failf "modulo by zero in constant expression" ()
    | `mod_ -> Ok (Z.rem sa sb) in (* §6.5.5 ¶6: (a/b)*b + a%b == a *)
  let* r = z_result in
  from_signed_z_checked ~bits r

let eval_iarith ~bits ~sign op a b = match (sign : Type.sign) with
  | Ssigned   -> eval_iarith_signed   ~bits op a b
  | Sunsigned -> eval_iarith_unsigned ~bits op a b

(* §6.5.7 (shifts), §6.5.10–12 (bitwise).

   For `<<`: §6.5.7 ¶4 says the result is the bit pattern shifted in
   if both operands are nonnegative and the result fits, otherwise
   UB. We additionally reject negative signed LHS, which is the
   common compiler-warning trigger.

   For `>>` with a negative signed LHS: §6.5.7 ¶5 makes the result
   implementation-defined; we use arithmetic right shift.
*)
let eval_ibitwise ~bits ~(sign : Type.sign) ~lhs_bits (op : Expr.bbitwise) a b =
  let module B = (val Bv.modular bits) in
  match op with
  | `and_ -> Ok B.(a land b)
  | `or_  -> Ok B.(a lor b)
  | `xor  -> Ok B.(a lxor b)
  | `shl ->
    let open E.Let in
    let* n = shift_count ~lhs_bits b in
    let lhs_signed_neg = match sign with
      | Type.Ssigned   -> Z.lt (to_signed_z ~bits:lhs_bits a) Z.zero
      | Type.Sunsigned -> false in
    if lhs_signed_neg then
      E.failf "left shift of a negative value in constant expression" ()
    else
      (* For signed nonnegative operand, surface overflow when
         a*2^n exceeds the signed range; §6.5.7 ¶4 makes that UB. *)
      begin match sign with
        | Sunsigned -> Ok B.(a lsl int n)
        | Ssigned ->
          let r = Z.shift_left (to_signed_z ~bits:lhs_bits a) n in
          from_signed_z_checked ~bits r
      end
  | `shr ->
    let open E.Let in
    let+ n = shift_count ~lhs_bits b in
    match sign with
    | Ssigned   -> B.(a asr int n)
    | Sunsigned -> B.(a lsr int n)

(* §6.5.8 (relational), §6.5.9 (equality): result is `int` 0 or 1. *)
let eval_icmp ~lhs_bits ~(lhs_sign : Type.sign) (op : Expr.cmp) a b = match op with
  | `eq -> Bv.(a = b)
  | `ne -> Bv.(a <> b)
  | #Expr.rel as r ->
    let c = match lhs_sign with
      | Ssigned   -> Bv.signed_compare a b lhs_bits
      | Sunsigned -> Bv.compare a b in
    match r with
    | `lt -> c <  0
    | `gt -> c >  0
    | `le -> c <= 0
    | `ge -> c >= 0

(* §6.5.3.3 (unary arithmetic):

   - [+]: identity on the promoted operand.
   - [-]: negative of the promoted operand; signed overflow when
          negating `INT_MIN` is UB (§6.5 ¶5).
   - [~]: bitwise complement of the promoted operand.
   - [!]: logical negation; result is `int` 0 or 1.
*)
let eval_iunary ~bits ~(sign : Type.sign) op v =
  let module B = (val Bv.modular bits) in
  match op with
  | `plus  -> Ok (Some (mask bits v))
  | `minus ->
    begin match sign with
      | Sunsigned -> Ok (Some (B.neg v))
      | Ssigned ->
        let open E.Let in
        let z = Z.neg (to_signed_z ~bits v) in
        let+ bv = from_signed_z_checked ~bits z in
        Some bv
    end
  | `not_  -> Ok (Some (B.lnot v))
  | `lnot_ -> Ok (Some (if is_truthy v then Bv.zero else Bv.one))
  | `deref -> Ok None

(* Float operators (§6.5 + Annex F for IEC 60559 binding) *)

let eval_farith (op : Expr.barith) a b =
  let open F32 in
  match op with
  | `add  -> Some (a + b)
  | `sub  -> Some (a - b)
  | `mul  -> Some (a * b)
  | `div  -> Some (a / b) (* IEEE: inf/NaN for /0 *)
  | `mod_ -> None (* §6.5.5 ¶2: integer operands only *)

(* §6.5.8 ¶6 / §6.5.9 ¶3: result is `int` 0/1.

   Annex F.8.3: an unordered (NaN-involving) comparison yields false
   except `!=`.
*)
let eval_fcmp (op : Expr.cmp) a b =
  let open F32 in
  let cmp k = not (is_nan a) && not (is_nan b) && k a b in
  match op with
  | `eq -> cmp (=)
  | `ne -> not (cmp (=))
  | `lt -> cmp (<)
  | `gt -> cmp (>)
  | `le -> cmp (<=)
  | `ge -> cmp (>=)

(* §6.5.3.3: unary on float operands. `!` and `~` are handled at the
   fold level.

   `~` is forbidden on floats and `!` yields `int`.
*)
let eval_funary op a =
  let open F32 in
  match op with
  | `plus -> Some a
  | `minus -> Some (neg a)
  | `not_ | `lnot_ | `deref -> None

let eval_darith (op : Expr.barith) a b =
  let open Float in
  match op with
  | `add  -> Some (a + b)
  | `sub  -> Some (a - b)
  | `mul  -> Some (a * b)
  | `div  -> Some (a / b)
  | `mod_ -> None

let eval_dcmp (op : Expr.cmp) a b =
  let open Float in
  let cmp k = not (is_nan a) && not (is_nan b) && k a b in
  match op with
  | `eq -> cmp (=)
  | `ne -> not (cmp (=))
  | `lt -> cmp (<)
  | `gt -> cmp (>)
  | `le -> cmp (<=)
  | `ge -> cmp (>=)

let eval_dunary op a = match op with
  | `plus -> Some a
  | `minus -> Some (Float.neg a)
  | `not_ | `lnot_ | `deref -> None

(* Folding  *)

open E.Let

let rec fold t (e : Texpr.t) : Texpr.t Or_error.t = match e.node with
  | Econst _ -> Ok e
  (* §6.4.4.3 ¶2: enumeration constants have type [int]; the value
     is already resolved by elaboration. *)
  | Eenum_const {value; _} ->
    let bits = D.int_bits t.dm in
    Ok (mk_int e.ty (mask bits value))
  (* Variables and function designators are not foldable. *)
  | Evar _ | Efun _ -> Ok e
  | Eunary {op; arg} ->
    let* arg' = fold t arg in
    fold_unary t e op arg'
  | Ebinary {op; lhs; rhs} ->
    let* lhs' = fold t lhs in
    let* rhs' = fold t rhs in
    fold_binary t e op lhs' rhs'
  | Ecast {dst; arg} ->
    let* arg' = fold t arg in
    fold_cast t e dst arg'
  (* §6.5.15 ¶4: the unevaluated branch contributes no value;
     §6.6 ¶3 says unevaluated subexpressions are exempt from the
     constant-expression constraints. We therefore only walk one
     branch when the condition is itself a known constant. *)
  | Econd {cond; then_; else_} ->
    let* cond' = fold t cond in
    begin match is_truthy_expr t cond' with
      | Some true  -> fold t then_
      | Some false -> fold t else_
      | None ->
        let* then_' = fold t then_ in
        let+ else_' = fold t else_ in
        Texpr.cond ~cond:cond' ~then_:then_' ~else_:else_' ~ty:e.ty
    end
  (* §6.6 ¶9: an address constant is `&` applied to an lvalue of
     static storage duration, or a function designator. We fold any
     expressions occurring inside the lvalue (e.g. array indices)
     but preserve the `Eaddrof` form. *)
  | Eaddrof tlv ->
    let+ tlv' = fold_lval t tlv in
    Texpr.addrof tlv' ~ty:e.ty
  | Eindex _ | Emember _ | Ecompound _ ->
    (* Aggregate and indexed rvalue constants are not folded here;
       only their address forms (handled via `Eaddrof` above) are
       supported initializer constants per §6.6 ¶9. *)
    Ok e

and fold_lval t (tlv : Texpr.tlval) =
  match tlv.node with
  | Lvar _ -> Ok tlv
  | Lderef e ->
    let+ e' = fold t e in
    Texpr.lderef e' ~ty:tlv.ty
  | Lmember {lval; field} ->
    let+ lval' = fold_lval t lval in
    Texpr.lmember ~lval:lval' ~field ~ty:tlv.ty
  | Lindex {lval; index} ->
    let* lval' = fold_lval t lval in
    let+ index' = fold t index in
    Texpr.lindex ~lval:lval' ~index:index' ~ty:tlv.ty

and fold_unary t e (op : Texpr.uop) (arg' : Texpr.t) =
  let unchanged () = Ok (Texpr.unary ~op ~arg:arg' ~ty:e.ty) in
  let (let$) x f = match x with
    | None -> unchanged ()
    | Some y -> f y in
  match float_kind arg'.ty with
  | Some `f32 ->
    let$ f = extract_f32 arg' in
    begin match op with
      | `lnot_ ->
        (* §6.5.3.3 ¶5: `!fp` is defined; the result is `int`. *)
        let truthy = F32.(f <> of_float 0.0) in
        Ok (mk_bool e.ty (not truthy))
      | _ ->
        let$ r = eval_funary op f in
        Ok (mk_f32 e.ty r)
    end
  | Some `f64 ->
    let$ d = extract_f64 arg' in
    begin match op with
      | `lnot_ -> Ok (mk_bool e.ty Float.(d = 0.0))
      | _ ->
        let$ r = eval_dunary op d in
        Ok (mk_f64 e.ty r)
    end
  | None ->
    let$ v = extract_int t arg' in
    let$ bits, sign = int_info t arg'.ty in
    let* r_opt = eval_iunary ~bits ~sign op v in
    let$ r = r_opt in
    Ok (mk_int e.ty r)

and fold_binary t e (op : Texpr.bop) (lhs' : Texpr.t) (rhs' : Texpr.t) =
  let unchanged () = Ok (Texpr.binary ~op ~lhs:lhs' ~rhs:rhs' ~ty:e.ty) in
  let (let$) x f = match x with
    | None -> unchanged ()
    | Some y -> f y in
  match float_kind lhs'.ty with
  | Some `f32 ->
    let$ a = extract_f32 lhs' in
    let$ b = extract_f32 rhs' in
    begin match op with
      | #Expr.barith as op ->
        let$ r = eval_farith op a b in
        Ok (mk_f32 e.ty r)
      | #Expr.cmp as op -> Ok (mk_bool e.ty (eval_fcmp op a b))
      | _ -> unchanged ()
    end
  | Some `f64 ->
    let$ a = extract_f64 lhs' in
    let$ b = extract_f64 rhs' in
    begin match op with
      | #Expr.barith as op ->
        let$ r = eval_darith op a b in
        Ok (mk_f64 e.ty r)
      | #Expr.cmp as op -> Ok (mk_bool e.ty (eval_dcmp op a b))
      | _ -> unchanged ()
    end
  | None ->
    let$ a = extract_int t lhs' in
    let$ b = extract_int t rhs' in
    let lhs_info = int_info t lhs'.ty in
    let res_info = int_info t e.ty in
    match op, lhs_info, res_info with
    | (#Expr.barith as op), _, Some (bits, sign) ->
      let+ r = eval_iarith ~bits ~sign op a b in
      mk_int e.ty r
    | (#Expr.bbitwise as op), Some (lhs_bits, _), Some (bits, sign) ->
      let+ r = eval_ibitwise ~bits ~sign ~lhs_bits op a b in
      mk_int e.ty r
    | (#Expr.cmp as op), Some (lhs_bits, lhs_sign), _ ->
      Ok (mk_bool e.ty (eval_icmp ~lhs_bits ~lhs_sign op a b))
    | _ -> unchanged ()

(* §6.6 ¶6 (ICE): casts must convert arithmetic types to integer
   types.

   §6.6 ¶8 (arith): arithmetic to arithmetic.

   §6.6 ¶7 (init): additional latitude for null pointer constants
   and address constants.
*)
and fold_cast t e (dst : Texpr.ty) (arg' : Texpr.t) =
  let unchanged () = Ok (Texpr.cast ~dst ~arg:arg') in
  let (let$) x f = match x with
    | None -> unchanged ()
    | Some y -> f y in
  let src_int = int_info t arg'.ty in
  let dst_int = int_info t dst in
  let src_flt = float_kind arg'.ty in
  let dst_flt = float_kind dst in
  match extract_int t arg', src_int, dst_int with
  (* int to int (§6.3.1.3). *)
  | Some v, Some (src_bits, src_sign), Some (dst_bits, _) ->
    Ok (mk_int e.ty (cast_int ~src_bits ~src_sign ~dst_bits v))
  | _ -> match src_flt, dst_flt with
    (* float to float (§6.3.1.5). *)
    | Some `f32, Some `f32 ->
      let$ f = extract_f32 arg' in
      Ok (mk_f32 e.ty f)
    | Some `f64, Some `f64 ->
      let$ d = extract_f64 arg' in
      Ok (mk_f64 e.ty d)
    | Some `f32, Some `f64 ->
      let$ f = extract_f32 arg' in
      Ok (mk_f64 e.ty @@ F32.to_float f)
    | Some `f64, Some `f32 ->
      let$ d = extract_f64 arg' in
      Ok (mk_f32 e.ty @@ F32.of_float d)
    (* int to float (§6.3.1.4 ¶2, §6.3.1.7). *)
    | None, Some `f32 ->
      let$ bits, sign = src_int in
      let$ v = extract_int t arg' in
      let$ f = int_to_f32 ~bits ~sign v in
      Ok (mk_f32 e.ty f)
    | None, Some `f64 ->
      let$ bits, sign = src_int in
      let$ v = extract_int t arg' in
      let$ d = int_to_f64 ~bits ~sign v in
      Ok (mk_f64 e.ty d)
    (* float to int (§6.3.1.4 ¶1). *)
    | Some `f32, _ ->
      let$ bits, sign = dst_int in
      let$ f = extract_f32 arg' in
      let+ r = f32_to_int ~bits ~sign f in
      mk_int e.ty r
    | Some `f64, _ ->
      let$ bits, sign = dst_int in
      let$ d = extract_f64 arg' in
      let+ r = f64_to_int ~bits ~sign d in
      mk_int e.ty r
    | _ -> unchanged ()

let int_const t e =
  let* e' = fold t e in
  match extract_int t e' with
  | None -> E.failf "expression does not reduce to an integer constant" ()
  | Some v -> Ok v

(* Address-constant recognition (§6.6 ¶7, ¶9) *)

(* §6.7.2.1: a [struct] or [union] tag names a compound type. *)
let compound_tag (ty : Texpr.ty) = match ty with
  | Tnamed {kind = #Type.compound; name; _} -> Some name
  | _ -> None

(* The pointee of a pointer type, or [None]. *)
let pointee_type (ty : Texpr.ty) = match ty with
  | Tptr {pointee; _} -> Some pointee
  | _ -> None

(* The element type of an array type, or [None]. *)
let array_elem (ty : Texpr.ty) = match ty with
  | Tarray {elem; _} -> Some elem
  | _ -> None

(* Encode a Z.t (which may be negative) as the bit pattern at `bits`
   width.

   Uses Euclidean remainder so the result is non-negative.
*)
let z_to_bv ~bits z =
  let m = Z.shift_left Z.one bits in
  Bv.bigint_unsafe (Z.erem z m)

(* Interpret a folded integer constant as a Z.t, sign-extended if its
   type is signed. *)
let idx_to_z t (e : Texpr.t) =
  let open O.Let in
  let* v = extract_int t e in
  let+ bits, sign = int_info t e.ty in
  match (sign : Type.sign) with
  | Ssigned   -> to_signed_z ~bits v
  | Sunsigned -> Bv.to_bigint v

(* §6.5.6 ¶8: pointer + integer scales the integer by the pointee
   size.

   Returns the scaled offset as a Z.t (signed) so the caller
   can combine it with a running offset before encoding.
*)
let rec ptr_offset_z t ptr_ty rhs_e =
  let open O.Let in
  let* n = idx_to_z t rhs_e in
  let* pointee = pointee_type ptr_ty in
  let+ sz = Result.ok (Layout.sizeof t.layout pointee) in
  Z.(n * of_int sz)

(* Computes (symbol, byte-offset Z) for the address of `tlv` when
   `tlv` designates an object of static storage duration, per §6.6 ¶9.

   Supports nested member access (§6.5.2.3), array indexing (§6.5.2.1),
   and the [&*p] cancellation.
*)
and lval_addr t (tlv : Texpr.tlval) : (string * Z.t) option =
  let open O.Let in
  match tlv.node with
  | Lvar name when TE.has_global t.tenv name -> Some (name, Z.zero)
  | Lvar name when TE.has_func t.tenv name -> Some (name, Z.zero)
  | Lvar _ -> None
  | Lmember {lval; field} ->
    let* sym, off = lval_addr t lval in
    let* tag = compound_tag lval.ty in
    let+ delta =
      Result.ok (Layout.offsetof t.layout ~tag ~field) in
    sym, Z.(off + of_int delta)
  | Lindex {lval; index} ->
    let* sym, off = lval_addr t lval in
    let* elem = array_elem lval.ty in
    let* sz = Result.ok (Layout.sizeof t.layout elem) in
    let+ n = idx_to_z t index in
    sym, Z.(off + n * of_int sz)
  | Lderef e -> expr_addr_z t e

(* Recognizes the address-constant forms permitted by §6.6 ¶7:

   - the address of a static-storage-duration lvalue ([&x]); and
   - an address constant plus or minus an integer constant expression
     (§6.5.6 / §6.6 ¶7).
*)
and expr_addr_z t (e : Texpr.t) : (string * Z.t) option =
  let open O.Let in
  match e.node with
  | Eaddrof tlv -> lval_addr t tlv
  | Ebinary {op = `add; lhs; rhs} when Type.is_pointer lhs.ty ->
    let* sym, off = expr_addr_z t lhs in
    let+ delta = ptr_offset_z t lhs.ty rhs in
    sym, Z.(off + delta)
  | Ebinary {op = `add; lhs; rhs} when Type.is_pointer rhs.ty ->
    (* Commutativity of pointer + int. *)
    let* sym, off = expr_addr_z t rhs in
    let+ delta = ptr_offset_z t rhs.ty lhs in
    sym, Z.(off + delta)
  | Ebinary {op = `sub; lhs; rhs} when Type.is_pointer lhs.ty ->
    let* sym, off = expr_addr_z t lhs in
    let+ delta = ptr_offset_z t lhs.ty rhs in
    sym, Z.(off - delta)
  | Ecast {arg; _} when Type.is_pointer e.ty && Type.is_pointer arg.ty ->
    (* §6.6 ¶9 permits pointer casts in forming an address constant, and
       every pointer-to-pointer conversion preserves the address value.

       Per §6.3.2.3, the following cases all compare equal:
       - ¶2 qualification e.g. `int *` -> `const int *`
       - ¶1 to/from `void *`
       - ¶7 object-to-object
       - ¶8 function-to-function

       The ¶7 alignment caveat concerns dereferencing the result, not the
       stored address, so the byte address is well-defined here.

       Integer-to-pointer casts are excluded by the `arg` pointer guard,
       and the null case is handled by `try_null_const`.
    *)
    expr_addr_z t arg
  | _ -> None

let try_addr_const t e =
  let open O.Let in
  let+ sym, off = expr_addr_z t e in
  let bits = D.pointer_bits t.dm in
  Vaddr {sym; off = z_to_bv ~bits off}

(* §6.3.2.3 ¶3: a null pointer constant is an integer constant
   expression with value 0, or such an expression cast to `void*`.

   Per §6.7.8 the same form is accepted as an initializer for any
   pointer type, so we strip pointer-typed casts.
*)
let try_null_const _t (e : Texpr.t) =
  if not (Type.is_pointer e.ty) then None else
    let rec strip (e : Texpr.t) = match e.node with
      | Ecast {arg; _} when Type.is_pointer e.ty -> strip arg
      | _ -> e in
    let inner = strip e in
    let is_zero = match inner.node with
      | Econst (Cint {value; _}) -> Bv.(value = zero)
      | Econst (Cchar c) -> Char.equal c '\000'
      | _ -> false in
    Option.some_if is_zero Vnull

(* Pull an integer or character literal out of a folded Texpr,
   returning the masked bit pattern.  Integer constants are admitted
   by every mode, so the caller chooses where the [Vint] is built. *)
let vint_value t (e' : Texpr.t) =
  let open O.Let in
  let* bits, _ = int_info t e'.ty in
  match e'.node with
  | Econst (Cint {value; _}) -> Some (mask bits value)
  | Econst (Cchar c) ->
    Some Bv.(int (Char.to_int c) mod modulus bits)
  | _ -> None

let const_ice (t : ice t) (e' : Texpr.t) : ice value Or_error.t =
  match vint_value t e' with
  | Some v -> Ok (Vint v)
  | None ->
    E.failf "expression does not reduce to an integer constant" ()

let const_arith (t : arith t) (e' : Texpr.t) : arith value Or_error.t =
  match vint_value t e' with
  | Some v -> Ok (Vint v)
  | None -> match e'.node with
    | Econst (Cfloat f)  -> Ok (Vfloat f)
    | Econst (Cdouble d) -> Ok (Vdouble d)
    | _ ->
      E.failf "expression does not reduce to an arithmetic constant" ()

(* §6.3.2.1 ¶3: a string literal initializing a pointer decays to the
   address of its first element.

   The decay is an explicit pointer-typed cast, so look through such
   casts to recover the literal.
*)
let rec strip_ptr_casts (e : Texpr.t) = match e.node with
  | Ecast {arg; _} when Type.is_pointer e.ty -> strip_ptr_casts arg
  | _ -> e

let const_init (t : init t) (e' : Texpr.t) : init value Or_error.t =
  match vint_value t e' with
  | Some v -> Ok (Vint v)
  | None -> match e'.node with
    | Econst Cfloat f  -> Ok (Vfloat f)
    | Econst Cdouble d -> Ok (Vdouble d)
    | Econst Cstr s    -> Ok (Vstring s)
    (* §6.5.2.5 ¶3 says a compound literal at file scope has
       static storage duration.

       Forming an address constant from one requires synthesizing an
       anonymous global, which should be the job of a pre-pass over
       the typed AST, not this module.
    *)
    | Ecompound _ ->
      E.failf "compound literals must be hoisted to anonymous \
               globals before constant evaluation" ()
    | _ -> match (strip_ptr_casts e').node with
      | Econst Cstr s -> Ok (Vstring s)
      | _ -> match try_null_const t e' with
        | Some v -> Ok v
        | None -> match try_addr_const t e' with
          | None -> E.failf "this expression is not a valid address constant" ()
          | Some v -> Ok v

let const : type m. m t -> Texpr.t -> m value Or_error.t = fun t e ->
  let* e' = fold t e in
  match t.mode with
  | Ice   -> (const_ice t e'   : m value Or_error.t)
  | Arith -> (const_arith t e' : m value Or_error.t)
  | Init  -> (const_init t e'  : m value Or_error.t)
