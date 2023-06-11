(** Arbitrary-precision bitvectors.

    For more documentation, see:

    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec/Bitvec/index.html }
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-binprot/Bitvec_binprot/index.html }
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-sexp/Bitvec_sexp/index.html}
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-order/Bitvec_order/index.html}
*)

open Core

include Bitvec
include Bitvec_binprot
include Bitvec_order
include Bitvec_sexp

let hash_fold_t st t = Hash.fold_string st @@ to_string t
