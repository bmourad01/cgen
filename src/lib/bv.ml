(** Arbitrary-precision bitvectors.

    For more documentation, see:

    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec/Bitvec/index.html}
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-binprot/Bitvec_binprot/index.html}
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-sexp/Bitvec_sexp/index.html}
    {:https://binaryanalysisplatform.github.io/bap/api/master/bitvec-order/Bitvec_order/index.html}
*)

include Bitvec
include Bitvec_binprot
include Bitvec_order
include Bitvec_sexp

include Core.Hashable.Make_and_derive_hash_fold_t(struct
    include Bitvec
    include Bitvec_sexp
  end)
