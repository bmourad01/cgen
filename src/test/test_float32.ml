open Core
open Cgen.Float32

module Q = Quickcheck

let gen_float32 = Q.Generator.map Int32.quickcheck_generator ~f:of_bits
let gen_pair = Q.Generator.both gen_float32 gen_float32

let f64 x = to_float x
let near ?(eps = 1e-5) a b = Float.(abs (f64 a - f64 b) <= eps)

let prop_add_approx a b =
  is_nan a || is_nan b || is_inf a || is_inf b ||
  let r = add a b in
  let e = of_float Float.(f64 a + f64 b) in
  is_nan r || is_inf r || is_nan e || is_inf e || near r e

let prop_sub_approx a b =
  is_nan a || is_nan b || is_inf a || is_inf b ||
  let r = sub a b in
  let e = of_float Float.(f64 a - f64 b) in
  is_nan r || is_inf r || is_nan e || is_inf e || near r e

let prop_mul_approx a b =
  is_nan a || is_nan b || is_inf a || is_inf b ||
  let r = mul a b in
  let e = of_float Float.(f64 a * f64 b) in
  is_nan r || is_inf r || is_nan e || is_inf e || near r e

let prop_div_approx a b =
  is_nan a || is_nan b || is_inf a || is_inf b || Float.(f64 b = 0.0) ||
  let r = div a b in
  let e = of_float Float.(f64 a / f64 b) in
  is_nan r || is_inf r || is_nan e || is_inf e || near r e

let prop_neg_approx x =
  let r = neg x in
  let fx = to_float x in
  let e = of_float Float.(-fx) in
  if is_nan x then is_nan r
  else if is_inf x
  then is_inf r && Bool.equal (is_negative r) (not @@ is_negative x)
  else near r e

let prop_compare_consistent a b =
  is_unordered a b ||
  let c = compare a b in
  let eq = Int.(c = 0) in
  let lt = Int.(c < 0) in
  let gt = Int.(c > 0) in
  Bool.equal eq (a = b) &&
  Bool.equal (not eq) (a <> b) &&
  Bool.equal lt (a < b) &&
  Bool.equal (lt || eq) (a <= b) &&
  Bool.equal gt (a > b) &&
  Bool.equal (gt || eq) (a >= b)

let prop_is_zero x = Bool.equal (is_zero x) Float.(f64 x = 0.0)

let prop_is_negative x =
  let sign_bit = Int32.(bits x land 0x8000_0000l <> 0l) in
  Bool.equal (is_negative x) sign_bit

let prop_is_inf x = Bool.equal (is_inf x) (Float.is_inf @@ f64 x)
let prop_is_nan x = Bool.equal (is_nan x) (Float.is_nan @@ f64 x)

let prop_bits_roundtrip x =
  let b = bits x in
  let x' = of_bits b in
  Int32.equal b (bits x')

let prop_string_roundtrip x =
  let s = to_string x in
  let x' = of_string s in
  if is_nan x then is_nan x'
  else if is_inf x
  then is_inf x' && Bool.(is_negative x = is_negative x')
  else not @@ is_nan x'

let prop_int_conversions x =
  ignore (to_int8   x  : int);
  ignore (to_int16  x  : int);
  ignore (to_int32  x  : int32);
  ignore (to_int64  x  : int64);
  ignore (to_uint8  x  : int);
  ignore (to_uint16 x  : int);
  ignore (to_uint32 x  : int32);
  ignore (to_uint64 x  : int64);
  ignore (of_int8   0  : t);
  ignore (of_int16  0  : t);
  ignore (of_int32  0l : t);
  ignore (of_int64  0L : t);
  ignore (of_uint8  0  : t);
  ignore (of_uint16 0  : t);
  ignore (of_uint32 0l : t);
  ignore (of_uint64 0L : t);
  true

(* prints failing inputs! *)
let qc1 name gen prop =
  match
    Q.test_or_error gen
      ~seed:(`Deterministic name)
      ~trials:5000
      ~f:(fun x ->
          if prop x then Ok ()
          else Or_error.error_s [%sexp "failed", (x : t)])
  with
  | Ok () -> ()
  | Error e -> Error.raise e

let qc2 name gen prop =
  match
    Q.test_or_error gen
      ~seed:(`Deterministic name)
      ~trials:5000
      ~f:(fun (a, b) ->
          if prop a b then Ok ()
          else Or_error.error_s [%sexp "failed", (a : t), (b : t)])
  with
  | Ok () -> ()
  | Error e -> Error.raise e

let%test_unit "bits roundtrip" = qc1 "bits" gen_float32 prop_bits_roundtrip
let%test_unit "add approx" = qc2 "add" gen_pair prop_add_approx
let%test_unit "sub approx" = qc2 "sub" gen_pair prop_sub_approx
let%test_unit "mul approx" = qc2 "mul" gen_pair prop_mul_approx
let%test_unit "div approx" = qc2 "div" gen_pair prop_div_approx
let%test_unit "neg approx" = qc1 "neg" gen_float32 prop_neg_approx
let%test_unit "compare consistency" = qc2 "cmp" gen_pair prop_compare_consistent
let%test_unit "is_zero" = qc1 "zero" gen_float32 prop_is_zero
let%test_unit "is_negative" = qc1 "neg" gen_float32 prop_is_negative
let%test_unit "is_inf" = qc1 "inf" gen_float32 prop_is_inf
let%test_unit "is_nan" = qc1 "nan" gen_float32 prop_is_nan
let%test_unit "int conversions" = qc1 "int" gen_float32 prop_int_conversions
let%test_unit "string roundtrip" = qc1 "str" gen_float32 prop_string_roundtrip
