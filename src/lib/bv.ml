(** Arbitrary-precision bitvectors.

    For more documentation, see:

    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec/Bitvec/index.html}
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-binprot/Bitvec_binprot/index.html}
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-sexp/Bitvec_sexp/index.html}
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-order/Bitvec_order/index.html}
*)

open Core

include Bitvec
include Bitvec_binprot
include Bitvec_order
include Bitvec_sexp

include Core.Hashable.Make_and_derive_hash_fold_t(struct
    include Bitvec
    include Bitvec_sexp
  end)

let signed_compare x y size =
  let m = modulus size in
  let xn = msb x mod m in
  let yn = msb y mod m in
  match xn, yn with
  | true, false -> -1
  | false, true -> 1
  | _ -> compare x y

let max x y = if x > y then x else y [@@inline]
let min x y = if x < y then x else y [@@inline]

let min_unsigned_value = zero
let max_unsigned_value size = ones mod modulus size [@@inline]

let min_signed_value size =
  let m = modulus size in
  (one lsl (int Int.(size - 1) mod m)) mod m
[@@inline]

let max_signed_value size =
  let m = modulus size in
  pred ((one lsl (int Int.(size - 1) mod m)) mod m) mod m
[@@inline]

let setbit x n m =
  x lor (one lsl (int n mod m) mod m) mod m
[@@inline]

let clrbit x n m =
  x land (lnot (one lsl (int n mod m) mod m) mod m) mod m
[@@inline]

let clz x n =
  let x = to_bigint x in
  if Z.equal x Z.zero then n
  else Int.(n - Z.numbits x)

let ctz x n =
  let x = to_bigint x in
  if Z.equal x Z.zero then n
  else Z.trailing_zeros x

let clo x n =
  let m = modulus n in
  clz (lnot x mod m) n

let cto x n =
  let m = modulus n in
  ctz (lnot x mod m) n

let popcnt x = Z.popcount @@ to_bigint x [@@inline]

(* XXX: we would want an actual "known bits" domain for
   stuff like this. *)
let must_be_zeros, must_be_ones =
  let must_be cmp lo hi size =
    let m = modulus size in
    let res = ref zero in
    for k = 0 to Int.(size - 1) do
      let k1 = int Int.(k + 1) mod m in
      let blo = (lo lsr k1) mod m in
      let bhi = (hi lsr k1) mod m in
      if blo = bhi && cmp lo k && cmp hi k then
        res := setbit !res k m
    done;
    !res in
  let one x k = Z.testbit (to_bigint x) k in
  let zero x k = not (one x k) in
  must_be zero, must_be one

let active_bits x n =
  let z = clz x n in
  Int.(n - z)
[@@inline]

let num_sign_bits x n =
  let m = modulus n in
  if msb x mod m then clo x n else clz x n

let significant_bits x n =
  let s = num_sign_bits x n in
  Int.(n - s + 1)
[@@inline]

let bits_set_from n lo =
  let m = modulus n in
  let nb = int lo mod m in
  let bit = one lsl nb mod m in
  let mask = pred bit mod m in
  lnot mask mod m

let high_bits_set n h =
  if Int.(h = 0) then zero
  else if Int.(h >= n) then max_unsigned_value n
  else
    let m = modulus n in
    let sh = setbit zero h m in
    let lo = (sh - one) mod m in
    let d = int Int.(n - h) mod m in
    (lo lsl d) mod m

let low_bits_set n l =
  if Int.(l = 0) then zero
  else if Int.(l >= n) then max_unsigned_value n
  else
    let m = modulus n in
    let sh = setbit zero l m in
    (sh - one) mod m

let sext v size size' =
  let m = modulus size' in
  let nb = int Int.(size - 1) mod m in
  let bit = one lsl nb mod m in
  ((v lxor bit mod m) - bit) mod m

let srem' x y size =
  let m = modulus size in
  let ax = abs x mod m and ay = abs y mod m in
  let r = rem ax ay mod m in
  if msb x mod m then neg r mod m else r
