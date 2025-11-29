open Core
open Cgen

module I = Bv_interval
module Q = Quickcheck

let gen_size =
  Q.Generator.small_positive_int |>
  Q.Generator.filter ~f:(fun n -> n > 0 && n <= 64)

let gen_small_size =
  Q.Generator.small_positive_int |>
  Q.Generator.filter ~f:(fun n -> n > 0 && n <= 8)

let gen_bv size =
  Q.Generator.map Int64.quickcheck_generator ~f:(fun x ->
      Bv.(int64 x mod modulus size))

let gen_interval size =
  Q.Generator.map (gen_bv size) ~f:(fun bv ->
      I.create_single ~value:bv ~size)

let gen_sized_interval =
  Q.Generator.bind gen_size ~f:(fun size ->
      gen_interval size |> Q.Generator.map
        ~f:(fun t -> size, t))

let gen_interval_pair =
  Q.Generator.bind gen_size ~f:(fun size ->
      Q.Generator.both (gen_interval size) (gen_interval size) |>
      Q.Generator.map ~f:(fun p -> size, p))

let gen_small_sized_interval =
  Q.Generator.bind gen_small_size ~f:(fun size ->
      gen_interval size |> Q.Generator.map
        ~f:(fun t -> size, t))

let gen_small_interval_pair =
  Q.Generator.bind gen_small_size ~f:(fun size ->
      Q.Generator.both (gen_interval size) (gen_interval size) |>
      Q.Generator.map ~f:(fun p -> size, p))

let all_bvs size =
  List.init (1 lsl size) ~f:(fun n -> Bv.(int n mod modulus size))

let concrete_values size t =
  all_bvs size |> List.filter ~f:(I.contains_value t)

let oracle_sound_binop ~size ~interval_op ~concrete_op t1 t2 =
  let vs1 = concrete_values size t1 in
  let vs2 = concrete_values size t2 in
  let results = List.bind vs1 ~f:(fun a ->
      let ia = Bv.to_int a in
      List.filter_map vs2 ~f:(fun b ->
          let ib = Bv.to_int b in
          concrete_op size ia ib |>
          Option.map ~f:(fun n ->
              Bv.(int n mod modulus size)))) in
  List.is_empty results ||
  let r_int = interval_op t1 t2 in
  List.for_all results ~f:(I.contains_value r_int)

let oracle_sound_unop ~size ~interval_op ~concrete_op t =
  let vs = concrete_values size t in
  let results = List.filter_map vs ~f:(fun v ->
      let i = Bv.to_int v in
      concrete_op size i |> Option.map ~f:(fun r ->
          Bv.(int r mod modulus size))) in
  List.is_empty results ||
  let t_int = interval_op t in
  List.for_all results ~f:(I.contains_value t_int)

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
  if b = 0 then None else
    let sa = to_signed size a in
    let sb = to_signed size b in
    if sb = 0 then None else
      let m = Bv.modulus size in
      let ba = Bv.(int sa mod m) in
      let bb = Bv.(int sb mod m) in
      let r = Bv.(srem ba bb mod m) in
      Some (Bv.to_int r)

let logand_mod _size a b = a land b
let logor_mod  _size a b = a lor b
let logxor_mod _size a b = a lxor b

let shl_opt size a b =
  if b >= size then None else Some ((a lsl b) land mask_of_size size)

let lshr_opt size a b =
  if b >= size then None else Some (a lsr b)

let ashr_opt size a b =
  if b >= size then None else
    let sa = to_signed size a in
    let shifted = sa asr b in
    Some (shifted land mask_of_size size)

let popcount size a =
  let a = a land mask_of_size size in
  let rec loop x acc = if x = 0 then acc
    else loop (x land (x - 1)) (acc + 1) in
  loop a 0

let bv_clz x n =
  let x = Bv.to_bigint x in
  let rec aux i =
    if i < 0 then n
    else if Z.testbit x i then n - i - 1
    else aux (i - 1) in
  aux (n - 1)

let bv_ctz x n =
  let x = Bv.to_bigint x in
  let rec aux i =
    if i >= n then n
    else if Z.testbit x i then i + 1
    else aux (i + 1) in
  aux 0

let clz size a = bv_clz Bv.(int a mod modulus size) size
let ctz size a = bv_ctz Bv.(int a mod modulus size) size

let prop_add_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.add
    ~concrete_op:(fun size a b -> Some (add_mod size a b))
    t1 t2

let prop_sub_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.sub
    ~concrete_op:(fun size a b -> Some (sub_mod size a b))
    t1 t2

let prop_mul_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.mul
    ~concrete_op:(fun size a b -> Some (mul_mod size a b))
    t1 t2

let prop_udiv_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.udiv
    ~concrete_op:udiv_opt
    t1 t2

let prop_urem_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.urem
    ~concrete_op:urem_opt
    t1 t2

let prop_sdiv_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.sdiv
    ~concrete_op:sdiv_opt
    t1 t2

let prop_srem_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.srem
    ~concrete_op:srem_opt
    t1 t2

let prop_logand_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.logand
    ~concrete_op:(fun size a b -> Some (logand_mod size a b))
    t1 t2

let prop_logor_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.logor
    ~concrete_op:(fun size a b -> Some (logor_mod size a b))
    t1 t2

let prop_logxor_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.logxor
    ~concrete_op:(fun size a b -> Some (logxor_mod size a b))
    t1 t2

let prop_lsl_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.logical_shift_left
    ~concrete_op:shl_opt
    t1 t2

let prop_lsr_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.logical_shift_right
    ~concrete_op:lshr_opt
    t1 t2

let prop_asr_sound (size, (t1, t2)) =
  oracle_sound_binop
    ~size
    ~interval_op:I.arithmetic_shift_right
    ~concrete_op:ashr_opt
    t1 t2

let prop_lnot_sound (size, t) =
  oracle_sound_unop
    ~size
    ~interval_op:I.lnot
    ~concrete_op:(fun size a -> Some ((lnot a) land mask_of_size size))
    t

let prop_neg_sound (size, t) =
  oracle_sound_unop
    ~size
    ~interval_op:I.neg
    ~concrete_op:(fun size a -> Some ((0 - a) land ((1 lsl size) - 1)))
    t

let prop_clz_sound (size, t) =
  oracle_sound_unop
    ~size
    ~interval_op:(I.clz ~zero_is_poison:false)
    ~concrete_op:(fun size a -> Some (clz size a))
    t

let prop_ctz_sound (size, t) =
  oracle_sound_unop
    ~size
    ~interval_op:(I.ctz ~zero_is_poison:false)
    ~concrete_op:(fun size a -> Some (ctz size a))
    t

let prop_popcnt_sound (size, t) =
  oracle_sound_unop
    ~size
    ~interval_op:I.popcnt
    ~concrete_op:(fun size a -> Some (popcount size a))
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
