open Core
open Cgen

module I = Bv_interval
module Q = Quickcheck
module G = Q.Generator

let gen_size =
  G.small_positive_int |>
  G.filter ~f:(fun n -> n > 0 && n <= 64)

let gen_small_size =
  G.small_positive_int |>
  G.filter ~f:(fun n -> n > 0 && n <= 8)

let gen_bv size =
  G.map Int64.quickcheck_generator ~f:(fun x ->
      Bv.(int64 x mod modulus size))

let gen_interval size =
  let gen_bv = gen_bv size in
  G.union [
    (* Singletons *)
    G.map gen_bv ~f:(fun v -> I.create_single ~value:v ~size);
    (* Non-wrapped *)
    G.map2 gen_bv gen_bv ~f:(fun a b ->
        if Bv.(a = b) then I.create_full ~size
        else if Bv.(a < b) then I.create ~lo:a ~hi:b ~size
        else I.create ~lo:b ~hi:a ~size);
    (* Wrapped ranges *)
    G.map2 gen_bv gen_bv ~f:(fun a b ->
        if Bv.(a = b) then I.create_full ~size
        else I.create ~lo:b ~hi:a ~size);
    (* Explicit full *)
    G.return (I.create_full ~size);
    (* Explicit empty *)
    G.return (I.create_empty ~size);
  ]

let gen_sized_interval =
  G.bind gen_size ~f:(fun size ->
      gen_interval size |>
      G.map ~f:(fun t -> size, t))

let gen_interval_pair =
  G.bind gen_size ~f:(fun size ->
      G.both (gen_interval size) (gen_interval size) |>
      G.map ~f:(fun p -> size, p))

let gen_small_sized_interval =
  G.bind gen_small_size ~f:(fun size ->
      gen_interval size |> G.map
        ~f:(fun t -> size, t))

let gen_small_sized_interval_size2 =
  G.bind gen_small_size ~f:(fun size ->
      gen_interval size |> G.map
        ~f:(fun t -> size, t)) |>
  G.map2 gen_small_size ~f:(fun k (size, t) -> size, t, k)

let gen_small_interval_pair =
  G.bind gen_small_size ~f:(fun size ->
      G.both (gen_interval size) (gen_interval size) |>
      G.map ~f:(fun p -> size, p))

let all_bvs size =
  List.init (1 lsl size) ~f:(fun n -> Bv.(int n mod modulus size))

let concrete_values size t =
  all_bvs size |> List.filter ~f:(I.contains_value t)

let oracle_sound_binop name ~size ~interval_op ~concrete_op t1 t2 =
  let r_int = interval_op t1 t2 in
  (* underdefined or overdefined result: just skip it *)
  I.is_empty r_int || I.is_full r_int ||
  let vs1 = concrete_values size t1 in
  let vs2 = concrete_values size t2 in
  let results = List.bind vs1 ~f:(fun a ->
      List.filter_map vs2 ~f:(fun b ->
          match concrete_op size (Bv.to_int a) (Bv.to_int b) with
          | None -> None   (* undefined: ignore *)
          | Some n -> Some (a,b, Bv.(int n mod modulus size)))) in
  List.for_all results ~f:(fun (a,b,r) ->
      let res = I.contains_value r_int r in
      if not res then
        Format.eprintf "%s(%a,%a) = %a: not in %a\n%!"
          name Bv.pp a Bv.pp b Bv.pp r I.pp r_int;
      res)

let oracle_sound_unop name ~size ~interval_op ~concrete_op t =
  let t_int = interval_op t in
  (* underdefined or overdefined result: just skip it *)
  I.is_empty t_int || I.is_full t_int ||
  let vs = concrete_values size t in
  let results = List.filter_map vs ~f:(fun v ->
      let i = Bv.to_int v in
      concrete_op size i |> Option.map ~f:(fun r ->
          v, Bv.(int r mod modulus size))) in
  List.is_empty results ||
  List.for_all results ~f:(fun (v, r) ->
      let res = I.contains_value t_int r in
      if not res then
        Format.eprintf "%s(%a): %a not in %a\n%!"
          name Bv.pp v Bv.pp r I.pp t_int;
      res)

let prop_size_preserved (size, t) = Int.equal size (I.size t)

let prop_bounds_valid (_size, t) =
  let lo = I.lower t in
  let hi = I.upper t in
  I.is_full t || I.is_empty t || not (Bv.equal lo hi)

let prop_empty_singleton_consistency (_size, t) =
  not (I.is_empty t) || begin
    Option.is_none (I.single_of t) &&
    not (I.is_single t)
  end

let prop_full_contains_all size =
  let t = I.create_full ~size in
  Q.test (gen_bv size)
    ~trials:100
    ~f:(fun bv -> assert (I.contains_value t bv));
  true

let prop_single_roundtrip size =
  Q.test (gen_bv size)
    ~trials:50
    ~f:(fun bv ->
        let t = I.create_single ~value:bv ~size in
        match I.single_of t with
        | Some bv' -> assert (Bv.equal bv bv')
        | None -> assert false);
  true

let prop_negative_nonnegative_disjoint (_size, t) =
  not (I.is_all_negative t && I.is_all_non_negative t)

let prop_binop_size_stable op (size, (t1, t2)) =
  try
    let r = op t1 t2 in
    Int.equal (I.size r) size
  with _ -> true

let prop_singleton_contains (_size, t) =
  match I.single_of t with
  | Some v -> I.contains_value t v
  | None -> true

let prop_contains_implies_single_contains (_size, (t1, t2)) =
  not (I.contains t1 t2) || match I.single_of t2 with
  | None -> true
  | Some v -> I.contains_value t1 v

let prop_intersect_comm (_size, (t1, t2)) =
  let r1 = I.intersect t1 t2 in
  let r2 = I.intersect t2 t1 in
  I.equal r1 r2

let prop_union_sound (_size, (t1, t2)) =
  let u1 = I.union t1 t2 in
  let u2 = I.union t2 t1 in
  I.contains u1 t1 &&
  I.contains u1 t2 &&
  I.contains u2 t1 &&
  I.contains u2 t2

let prop_inverse_involutive (_size, t) =
  I.equal (I.inverse (I.inverse t)) t

let prop_extract_shrinks (size,t) =
  if size > 1 then
    let hi = size - 1 in
    let lo = size / 2 in
    let t' = I.extract t ~hi ~lo in
    I.size t' = hi - lo + 1
  else true

let prop_concat_size ((size1, t1), (size2, t2)) =
  let t = I.concat t1 t2 in
  Int.equal (I.size t) (size1 + size2)

let mask_of_size size = (1 lsl size) - 1
let add_mod size a b = (a + b) land mask_of_size size
let sub_mod size a b = (a - b) land mask_of_size size
let mul_mod size a b = (a * b) land mask_of_size size
let udiv_opt _size a b = if b = 0 then None else Some (a / b)
let urem_opt _size a b = if b = 0 then None else Some (a mod b)

let to_signed size n =
  let sign_bit = 1 lsl (size - 1) in
  if (n land sign_bit) = 0 then n
  else n - (1 lsl size)

let sdiv_opt size a b =
  if b = 0 then None else
    let sa = to_signed size a in
    let sb = to_signed size b in
    if sb = 0 then None else
      let q = sa / sb in
      (* re-wrap as unsigned *)
      let res = q land mask_of_size size in
      Some res

let srem_opt size a b =
  if a = 0 || b = 0 then None else
    let m = Bv.modulus size in
    let a = Bv.(int a mod m) in
    let b = Bv.(int b mod m) in
    let r = Bv.srem' a b size in
    Some (Bv.to_int r)

let logand_mod size a b = (a land b) land mask_of_size size
let logor_mod  size a b = (a lor  b) land mask_of_size size
let logxor_mod size a b = (a lxor b) land mask_of_size size

let shl_opt size a b =
  if b >= size then None else Some ((a lsl b) land mask_of_size size)

let lshr_opt size a b =
  if b >= size then None else Some (a lsr b)

let ashr_opt size a b =
  if b >= size then None else
    let sa = to_signed size a in
    let shifted = sa asr b in
    Some (shifted land mask_of_size size)

let popcount size a = Bv.(popcnt (int a mod modulus size))
let clz size a = Bv.clz Bv.(int a mod modulus size) size
let ctz size a = Bv.ctz Bv.(int a mod modulus size) size

let prop_add_sound (size, (t1, t2)) =
  oracle_sound_binop "add"
    ~size
    ~interval_op:I.add
    ~concrete_op:(fun size a b -> Some (add_mod size a b))
    t1 t2

let prop_sub_sound (size, (t1, t2)) =
  oracle_sound_binop "sub"
    ~size
    ~interval_op:I.sub
    ~concrete_op:(fun size a b -> Some (sub_mod size a b))
    t1 t2

let prop_mul_sound (size, (t1, t2)) =
  oracle_sound_binop "mul"
    ~size
    ~interval_op:I.mul
    ~concrete_op:(fun size a b -> Some (mul_mod size a b))
    t1 t2

let prop_udiv_sound (size, (t1, t2)) =
  oracle_sound_binop "udiv"
    ~size
    ~interval_op:I.udiv
    ~concrete_op:udiv_opt
    t1 t2

let prop_urem_sound (size, (t1, t2)) =
  oracle_sound_binop "urem"
    ~size
    ~interval_op:I.urem
    ~concrete_op:urem_opt
    t1 t2

let prop_sdiv_sound (size, (t1, t2)) =
  oracle_sound_binop "sdiv"
    ~size
    ~interval_op:I.sdiv
    ~concrete_op:sdiv_opt
    t1 t2

let prop_srem_sound (size, (t1, t2)) =
  oracle_sound_binop "srem"
    ~size
    ~interval_op:I.srem
    ~concrete_op:srem_opt
    t1 t2

let prop_logand_sound (size, (t1, t2)) =
  oracle_sound_binop "logand"
    ~size
    ~interval_op:I.logand
    ~concrete_op:(fun size a b -> Some (logand_mod size a b))
    t1 t2

let prop_logor_sound (size, (t1, t2)) =
  oracle_sound_binop "logor"
    ~size
    ~interval_op:I.logor
    ~concrete_op:(fun size a b -> Some (logor_mod size a b))
    t1 t2

let prop_logxor_sound (size, (t1, t2)) =
  oracle_sound_binop "logxor"
    ~size
    ~interval_op:I.logxor
    ~concrete_op:(fun size a b -> Some (logxor_mod size a b))
    t1 t2

let prop_lsl_sound (size, (t1, t2)) =
  oracle_sound_binop "lsl"
    ~size
    ~interval_op:I.logical_shift_left
    ~concrete_op:shl_opt
    t1 t2

let prop_lsr_sound (size, (t1, t2)) =
  oracle_sound_binop "lsr"
    ~size
    ~interval_op:I.logical_shift_right
    ~concrete_op:lshr_opt
    t1 t2

let prop_asr_sound (size, (t1, t2)) =
  oracle_sound_binop "asr"
    ~size
    ~interval_op:I.arithmetic_shift_right
    ~concrete_op:ashr_opt
    t1 t2

let prop_lnot_sound (size, t) =
  oracle_sound_unop "lnot"
    ~size
    ~interval_op:I.lnot
    ~concrete_op:(fun size a -> Some ((lnot a) land mask_of_size size))
    t

let prop_neg_sound (size, t) =
  oracle_sound_unop "neg"
    ~size
    ~interval_op:I.neg
    ~concrete_op:(fun size a -> Some ((0 - a) land ((1 lsl size) - 1)))
    t

let prop_clz_sound (size, t) =
  oracle_sound_unop "clz"
    ~size
    ~interval_op:(I.clz ~zero_is_poison:false)
    ~concrete_op:(fun size a -> Some (clz size a))
    t

let prop_ctz_sound (size, t) =
  oracle_sound_unop "ctz"
    ~size
    ~interval_op:(I.ctz ~zero_is_poison:false)
    ~concrete_op:(fun size a -> Some (ctz size a))
    t

let prop_popcnt_sound (size, t) =
  oracle_sound_unop "popcnt"
    ~size
    ~interval_op:I.popcnt
    ~concrete_op:(fun size a -> Some (popcount size a))
    t

let prop_truncate_sound (size, t, k) =
  k < 0 || k >= size ||
  oracle_sound_unop "trunc"
    ~size:k
    ~interval_op:(fun _ -> I.trunc t ~size:k)
    ~concrete_op:(fun _size a ->
        let modulus = 1 lsl k in
        Some (a land (modulus - 1)))
    t

let oracle_sound_extension name ~from_size ~to_size ~concrete_op ~interval_op t =
  let t' = interval_op t in
  I.is_empty t' || I.is_full t' ||
  let vs = concrete_values from_size t in
  List.is_empty vs || List.for_all vs ~f:(fun v ->
      let w = concrete_op v from_size to_size in
      let res = I.contains_value t' w in
      if not res then
        Format.eprintf "%s(%a) = %a: not in %a\n%!"
          name Bv.pp v Bv.pp w I.pp t';
      res)

let prop_sext_sound (size, t, k) =
  k < 0 || k <= size ||
  oracle_sound_extension "sext" ~from_size:size ~to_size:k
    ~interval_op:(fun t -> I.sext t ~size:k)
    ~concrete_op:Bv.sext
    t

let prop_zext_sound (size, t, k) =
  k < 0 || k <= size ||
  oracle_sound_extension "zext" ~from_size:size ~to_size:k
    ~interval_op:(fun t -> I.zext t ~size:k)
    ~concrete_op:(fun v _ _ -> v)
    t

let qc1 sexp name gen prop =
  match
    Q.test_or_error gen
      ~seed:(`Deterministic name)
      ~trials:3000
      ~f:(fun x -> if prop x then Ok () else
             Or_error.error_s Sexp.(List [Atom "failed"; sexp x]))
  with Ok () -> () | Error e -> Error.raise e

let sexp_binop x = [%sexp (x : int * (I.t * I.t))]
let sexp_unop x = [%sexp (x : int * I.t)]
let sexp_unop_size x = [%sexp (x : int * I.t * int)]

let%test_unit "add preserves size" =
  qc1 sexp_binop "add-size" gen_interval_pair (prop_binop_size_stable I.add)

let%test_unit "sub preserves size" =
  qc1 sexp_binop "sub-size" gen_interval_pair (prop_binop_size_stable I.sub)

let%test_unit "mul preserves size" =
  qc1 sexp_binop "mul-size" gen_interval_pair (prop_binop_size_stable I.mul)

let%test_unit "size preserved" =
  qc1 sexp_unop "size" gen_sized_interval prop_size_preserved

let%test_unit "bounds valid" =
  qc1 sexp_unop "bounds" gen_sized_interval prop_bounds_valid

let%test_unit "singleton roundtrip" =
  qc1 sexp_of_int "single" gen_size prop_single_roundtrip

let%test_unit "empty singleton consistency" =
  qc1 sexp_unop "empty-single" gen_sized_interval prop_empty_singleton_consistency

let%test_unit "intersect commutative" =
  qc1 sexp_binop "intersect-comm" gen_interval_pair prop_intersect_comm

let%test_unit "union commutative" =
  qc1 sexp_binop "union-comm" gen_interval_pair prop_union_sound

let%test_unit "inverse involutive" =
  qc1 sexp_unop "inverse" gen_sized_interval prop_inverse_involutive

let%test_unit "contains → contains single" =
  qc1 sexp_binop "contains-single" gen_interval_pair prop_contains_implies_single_contains

let%test_unit "add sound" =
  qc1 sexp_binop "bv-add" gen_small_interval_pair prop_add_sound

let%test_unit "sub sound" =
  qc1 sexp_binop "bv-sub" gen_small_interval_pair prop_sub_sound

let%test_unit "mul sound" =
  qc1 sexp_binop "bv-mul" gen_small_interval_pair prop_mul_sound

let%test_unit "udiv sound" =
  qc1 sexp_binop "bv-udiv" gen_small_interval_pair prop_udiv_sound

let%test_unit "urem sound" =
  qc1 sexp_binop "bv-urem" gen_small_interval_pair prop_urem_sound

let%test_unit "sdiv sound" =
  qc1 sexp_binop "bv-sdiv" gen_small_interval_pair prop_sdiv_sound

let%test_unit "srem sound" =
  qc1 sexp_binop "bv-srem" gen_small_interval_pair prop_srem_sound

let%test_unit "logand sound" =
  qc1 sexp_binop "bv-logand" gen_small_interval_pair prop_logand_sound

let%test_unit "logor sound" =
  qc1 sexp_binop "bv-logor" gen_small_interval_pair prop_logor_sound

let%test_unit "logxor sound" =
  qc1 sexp_binop "bv-logxor" gen_small_interval_pair prop_logxor_sound

let%test_unit "lsl sound" =
  qc1 sexp_binop "bv-lsl" gen_small_interval_pair prop_lsl_sound

let%test_unit "lsr sound" =
  qc1 sexp_binop "bv-lsr" gen_small_interval_pair prop_lsr_sound

let%test_unit "asr sound" =
  qc1 sexp_binop "bv-asr" gen_small_interval_pair prop_asr_sound

let%test_unit "neg sound" =
  qc1 sexp_unop "bv-neg" gen_small_sized_interval prop_neg_sound

let%test_unit "lnot sound" =
  qc1 sexp_unop "bv-lnot" gen_small_sized_interval prop_lnot_sound

let%test_unit "clz sound" =
  qc1 sexp_unop "bv-clz" gen_small_sized_interval prop_clz_sound

let%test_unit "ctz sound" =
  qc1 sexp_unop "bv-ctz" gen_small_sized_interval prop_ctz_sound

let%test_unit "popcnt sound" =
  qc1 sexp_unop "bv-popcnt" gen_small_sized_interval prop_popcnt_sound

let%test_unit "trunc sound" =
  qc1 sexp_unop_size "bv-trunc" gen_small_sized_interval_size2 prop_truncate_sound

let%test_unit "sext sound" =
  qc1 sexp_unop_size "bv-sext" gen_small_sized_interval_size2 prop_sext_sound

let%test_unit "zext sound" =
  qc1 sexp_unop_size "bv-zext" gen_small_sized_interval_size2 prop_zext_sound
