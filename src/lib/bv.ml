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
  let rec aux i =
    if Int.(i < 0) then n
    else if Z.testbit x i then Int.(n - i - 1)
    else aux Int.(i - 1) in
  aux Int.(n - 1)

let ctz x n =
  let x = to_bigint x in
  if Z.equal x Z.zero then n
  else Z.trailing_zeros x

let clo x n =
  let x = to_bigint x in
  let rec aux i =
    if Int.(i < 0) then n
    else if not (Z.testbit x i) then Int.(n - i - 1)
    else aux Int.(i - 1) in
  aux Int.(n - 1)

let cto x n =
  let x = to_bigint x in
  let rec aux i =
    if Int.(i >= n) then n
    else if not (Z.testbit x i) then i
    else aux Int.(i + 1) in
  aux 0

let popcnt x = Z.popcount @@ to_bigint x [@@inline]

(* XXX: we would want an actual "known bits" domain for
   stuff like this. *)
let must_be_zeros, must_be_ones =
  let must_be cmp lo hi size =
    let module B = (val modular size) in
    let res = ref zero in
    for k = 0 to Int.(size - 1) do
      let open B in
      let bit1 = one lsl (int Int.(k + 1)) in
      let lo_block = lo / bit1 in
      let hi_block = hi / bit1 in
      if lo_block = hi_block then
        let bit = one lsl (int k) in
        let lo_bit = cmp (lo land bit) in
        let hi_bit = cmp (hi land bit) in
        if lo_bit && hi_bit then res := !res lor bit
    done;
    !res in
  must_be ((=)  zero),
  must_be ((<>) zero)

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
