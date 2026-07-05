open Core
open Cgen

module Bv = Cgen_utils.Bv
module Q = Quickcheck
module G = Q.Generator

(* Divisibility correctness *)

let imm_of_sz = function
  | 8 -> `i8
  | 16 -> `i16
  | 32 -> `i32
  | 64 -> `i64
  | _ -> assert false

let signed_z bv sz =
  let z = Bv.to_bigint bv in
  if Z.testbit z (sz - 1) then Z.(z - (one lsl sz)) else z

let truth ~signed ~sz x d =
  let xz = if signed then signed_z x sz else Bv.to_bigint x in
  let dz = if signed then signed_z d sz else Bv.to_bigint d in
  (not (Z.equal dz Z.zero)) && Z.equal (Z.rem xz dz) Z.zero

let eval ~sz (params : Magic_div.divisible) x =
  let module B = (val Bv.modular sz) in
  match params with
  | Pow2_mask mask -> Bv.(B.(x land mask) = zero)
  | Test {factor; bias; rot; limit} ->
    let p = B.(x * factor) in
    let p = B.(p + bias) in
    let p =
      if rot = 0 then p
      else B.((p lsr int rot) lor (p lsl int Int.(sz - rot))) in
    Bv.(p <= limit)

let fires ~signed ~sz d =
  let module B = (val Bv.modular sz) in
  Bv.(d <> B.zero)
  && Bv.(d <> B.one)
  && not (signed && Bv.(d = B.(pred zero)))

let ok ~signed ~sz d x =
  let params = Magic_div.divisible ~signed d (imm_of_sz sz) in
  Bool.equal (eval ~sz params x) (truth ~signed ~sz x d)

let%test_unit "divisible W=8 exhaustive (all divisors, all x, both signs)" =
  let sz = 8 in
  List.iter [false; true] ~f:(fun signed ->
      for di = 0 to (1 lsl sz) - 1 do
        let d = Bv.(int di mod modulus sz) in
        if fires ~signed ~sz d then
          for xi = 0 to (1 lsl sz) - 1 do
            let x = Bv.(int xi mod modulus sz) in
            if not (ok ~signed ~sz d x) then
              failwithf "W=8 signed:%b d:%d x:%d" signed di xi ()
          done
      done)

let gen_bv size =
  G.map Int64.quickcheck_generator ~f:(fun x ->
      Bv.(int64 x mod modulus size))

let gen_case =
  let open G in
  of_list [8; 16; 32; 64] >>= fun sz ->
  bool >>= fun signed ->
  let g = gen_bv sz in
  both (filter g ~f:(fun d -> fires ~signed ~sz d)) g >>| fun (d, x) ->
  signed, sz, d, x

let sexp_of_case (signed, sz, d, x) =
  [%message "" (signed : bool) (sz : int) (d : Bv.t) (x : Bv.t)]

let%test_unit "divisible W=8,16,32,64" =
  Q.test gen_case
    ~sexp_of:sexp_of_case
    ~trials:200_000
    ~f:(fun (signed, sz, d, x) ->
        if not (ok ~signed ~sz d x) then
          failwiths ~here:[%here] "mismatch" (signed, sz, d, x) sexp_of_case)

(* Magic-division correctness *)

let wrap sz z = Z.logand z Z.(shift_left one sz - one)
let sval sz z = if Z.testbit z (sz - 1) then Z.(z - shift_left one sz) else z
let is_pow2 z = Z.gt z Z.zero && Z.equal (Z.logand z (Z.pred z)) Z.zero

let udiv_quotient ~sz x (mbv, add, shr) =
  let m = Bv.to_bigint mbv in
  let x = wrap sz x in
  let q1 = wrap sz (Z.shift_right Z.(x * m) sz) in
  if add then
    let t = wrap sz (Z.shift_right (wrap sz Z.(x - q1)) 1) in
    wrap sz (Z.shift_right (wrap sz Z.(t + q1)) (shr - 1))
  else if shr > 0 then wrap sz (Z.shift_right q1 shr)
  else q1

let sdiv_quotient ~sz ~d x (mbv, shr) =
  let x = wrap sz x and m = wrap sz (Bv.to_bigint mbv) and d = wrap sz d in
  let msb z = Z.testbit z (sz - 1) in
  let q1 = wrap sz (Z.shift_right Z.(sval sz x * sval sz m) sz) in
  let q2 =
    if (not (msb d)) && msb m then wrap sz Z.(q1 + x)
    else if msb d && not (msb m) then wrap sz Z.(q1 - x)
    else q1 in
  let q3 = if shr = 0 then q2 else wrap sz (Z.shift_right (sval sz q2) shr) in
  wrap sz Z.(q3 + (if msb q3 then one else zero))

let valid_divisor ~signed ~sz dbv =
  let d = Bv.to_bigint dbv in
  let ad = if signed then Z.abs (sval sz d) else d in
  Z.gt ad Z.one && not (is_pow2 ad)

let magic_ok ~signed ~sz dbv xbv =
  let ty = imm_of_sz sz in
  let x = Bv.to_bigint xbv and d = Bv.to_bigint dbv in
  if signed then
    let got = sval sz (sdiv_quotient ~sz ~d x (Magic_div.signed dbv ty)) in
    let want = Z.div (sval sz x) (sval sz d) in
    Z.equal got want
  else
    let got = udiv_quotient ~sz x (Magic_div.unsigned dbv ty) in
    Z.equal got (Z.div x d)

let%test_unit "Magic_div correct, W=8 exhaustive (non-pow2, both signs)" =
  let sz = 8 in
  List.iter [false; true] ~f:(fun signed ->
      for di = 0 to (1 lsl sz) - 1 do
        let dbv = Bv.(int di mod modulus sz) in
        if valid_divisor ~signed ~sz dbv then
          for xi = 0 to (1 lsl sz) - 1 do
            let xbv = Bv.(int xi mod modulus sz) in
            if not (magic_ok ~signed ~sz dbv xbv) then
              failwithf "magic W=8 signed:%b d:%d x:%d" signed di xi ()
          done
      done)

let gen_magic_case =
  let open G in
  of_list [8; 16; 32; 64] >>= fun sz ->
  bool >>= fun signed ->
  let g = gen_bv sz in
  both (filter g ~f:(valid_divisor ~signed ~sz)) g >>| fun (d, x) ->
  signed, sz, d, x

let%test_unit "Magic_div.{unsigned,signed} correct, W in {8,16,32,64}" =
  Q.test gen_magic_case
    ~sexp_of:sexp_of_case
    ~trials:200_000
    ~f:(fun (signed, sz, d, x) ->
        if not (magic_ok ~signed ~sz d x) then
          failwiths ~here:[%here] "magic mismatch" (signed, sz, d, x) sexp_of_case)
