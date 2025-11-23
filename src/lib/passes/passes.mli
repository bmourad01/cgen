(** The compiler passes for [Virtual] programs. *)

open Core
open Virtual

(** Runs type-checking and SSA transformation. *)
val initialize : module_ -> (Typecheck.env * module_) Context.t

(** Runs the middle-end optimizations in the recommended order. *)
val optimize : Typecheck.env -> module_ -> (Typecheck.env * module_) Context.t

(** Performs ABI lowering on the entire module. *)
val to_abi : Typecheck.env -> module_ -> Abi.module_ Context.t

(** Runs the middle-end optimizations in the recommended order, for an
    ABI-lowered module. *)
val optimize_abi : Abi.module_ -> Abi.module_ Context.t

(** Runs instruction selection on the ABI-lowered module according to the
    provided machine implementation.

    Will fail if the provided machine interface is not the same target
    as that of the current context (see [Context.target]).
*)
val isel :
  (module Machine_intf.S
    with type Reg.t = 'r
     and type Insn.t = 'i) ->
  Abi.module_ ->
  ('i, 'r) Pseudo.module_ Context.t

(** Runs register allocation on the pseudo-assembly module according to the
    provided machine implementation.

    Will fail if the provided machine interface is not the same target
    as that of the current context (see [Context.target]).
*)
val regalloc :
  (module Machine_intf.S
    with type Reg.t = 'r
     and type Insn.t = 'i) ->
  ('i, 'r) Pseudo.module_ ->
  ('i, 'r) Pseudo.module_ Context.t

(** Lowers the ABI module to target-specific assembly code, and prints it
    to the provided formatter. *)
val to_asm : Format.formatter -> Abi.module_ -> unit Context.t

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
module Abi_loadopt : sig
  val run : Abi.func -> Abi.func Or_error.t
end

(** Attempts to coalesce slots of compatible size and alignment which
    do not interfere (i.e. are never live at the same time).

    Assumes the function is in SSA form.
*)
module Coalesce_slots : sig
  val run : func -> func Or_error.t
  val run_abi : Abi.func -> Abi.func Or_error.t
end

(** Uses the [Egraph] module to perform a variety of optimizations
    to a function.

    The function is assumed to be in SSA form.
*)
module Egraph_opt : sig
  val run : Typecheck.env -> func -> func Context.t

  (** Runs the pass with no rewrite rules. *)
  val run_no_rules : Typecheck.env -> func -> func Context.t
end

(** This pass lowers a Virtual function into a Virtual ABI function,
    where parameter passing, compound types, and platform-specific
    constructs in Virtual are desugared and made to comform to a
    specific ABI.

    The function is assumed to be in SSA form, and the transformed
    function is expected to preserve it, modulo the presence of
    explicit registers.
*)
module Lower_abi : sig
  val run : Typecheck.env -> func -> Abi.func Context.t
end

(** Attempts to promote uniform stack slots to SSA variables.

    Assumes the function is in SSA form.
*)
module Promote_slots : sig
  val run : func -> func Or_error.t
  val run_abi : Abi.func -> Abi.func Or_error.t
end

(** Removes assignments to variables that are never used.

    The function is assumed to be in SSA form.
*)
module Remove_dead_vars : sig
  val run : func -> func Or_error.t
  val run_abi : Abi.func -> Abi.func Or_error.t
end

(** Removes all the blocks from a function that are unreachable
    from the entry block. *)
module Remove_disjoint_blks : sig
  val run : func -> func
  val run_abi : Abi.func -> Abi.func
end

(** Runs a data-flow analysis to determine block arguments
    that are constant.

    The function must be in SSA form.
*)
module Resolve_constant_blk_args : sig
  val run : func -> func Or_error.t
  val run_abi : Abi.func -> Abi.func Or_error.t
end

(** Performs the classic Sparse Conditional Constant
    Propagation (SCCP) pass.

    The function is assumed to be in SSA form.
*)
module Sccp : sig
  val run : Typecheck.env -> func -> func Or_error.t
end

(** Performs block merging, edge contraction, and other
    control-flow simplifications.

    The function must be in SSA form.
*)
module Simplify_cfg : sig
  val run : Typecheck.env -> func -> func Context.t
end

(** Performs Scalar Replacement of Aggregates (SROA).

    This aims to analyze access patterns of stack slots
    and break them up into individual (scalar) components.

    An important detail to note is that in the non-ABI pass,
    slots being referenced in terms of user-defined compound
    (aggregate) types are treated as opaque, and therefore
    not optimized, as these are often ABI-dependent.

    When ABI lowering is performed, these references should
    be desugared into access patterns on primitive types,
    at which point the algorithm can attempt to process them.
*)
module Sroa : sig
  val run : func -> func Context.t
  val run_abi : Abi.func -> Abi.func Context.t
end

(** Transforms a function into semi-pruned SSA form. *)
module Ssa : sig
  val run : func -> func Or_error.t
  val run_abi : Abi.func -> Abi.func Or_error.t

  (** Verify that the function satisfies the invariants
      of SSA form. *)
  val check : func -> unit Or_error.t

  val check_abi : Abi.func -> unit Or_error.t
end
