(** Performs store-to-load forwarding and redundant load elimination
    on an ABI-lowered function (and some canonicalization of instruction
    operands in the process, which includes copy propagation).

    This is a similar optimization to what happens in [Egraph_opt], but
    with less overhead.

    The lowering applied in [Lower_abi] may generate excessive loads and
    stores, as well as additional stack slots that these operations are
    applied to (especially in the presence of compound types). This pass
    aims to simplify that generated code.

    The function must be in SSA form.
*)

open Core
open Virtual

val run : Abi.func -> Abi.func Or_error.t
