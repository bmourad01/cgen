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

let signed_compare x y m = match msb x mod m, msb y mod m with
  | true, true -> compare y x
  | false, false -> compare x y
  | true, false -> -1
  | false, true -> 1

let max x y = if x > y then x else y [@@inline]
let min x y = if x < y then x else y [@@inline]

let min_unsigned_value = zero
let max_unsigned_value size = ones mod modulus size [@@inline]

let min_signed_value size =
  let m = modulus size in
  (one lsl (int Int.(size - 1) mod m)) mod m

let max_signed_value size =
  let m = modulus size in
  pred ((one lsl (int Int.(size - 1) mod m)) mod m) mod m
