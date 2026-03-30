(** The compiler passes for [Virtual] programs. *)

open Core
open Virtual

(** Lowers from [Structured] to [Virtual]. *)
val destructure : Structured.module_ -> Virtual.module_ Context.t

(** Lifts from [Virtual] to [Structured]. *)
val restructure : tenv:Typecheck.env -> Virtual.module_ -> Structured.module_ Context.t

(** Runs type-checking and SSA transformation. *)
val initialize : module_ -> (Typecheck.env * module_) Context.t

(** Runs the middle-end optimizations in the recommended order. *)
val optimize : Typecheck.env -> module_ -> (Typecheck.env * module_) Context.t

(** Performs ABI lowering on the entire module. *)
val to_abi : Typecheck.env -> module_ -> Abi.module_ Context.t

(** Runs the middle-end optimizations in the recommended order, for an
    ABI-lowered module.

    When [invariants] is [true], SSA invariants are verified after the
    pass completes. Defaults to [false].
*)
val optimize_abi : ?invariants:bool -> Abi.module_ -> Abi.module_ Context.t

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

    When [invariants] is [true], internal invariant checking is enabled
    during register allocation. This is expensive and intended for
    development and testing; it defaults to [false].
*)
val regalloc :
  ?invariants:bool ->
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

    The motivation for this pass follows from the fact that transformations
    applied in [Lower_abi] may generate excessive loads and stores, as well as
    additional stack slots that these operations are applied to (especially
    in the presence of compound types). This pass aims to simplify that
    generated code.

    The function must be in SSA form.
*)
module Abi_loadopt : sig
  val run : Abi.func -> Abi.func Or_error.t
end

(** Attempts to coalesce slots of compatible size and alignment which
    do not interfere (i.e. are never live at the same time).

    As a result of analyzing access patterns of slots, this pass is
    also able to delete slots that are only ever stored to.

    Assumes the function is in SSA form.
*)
module Coalesce_slots : sig
  val run : func -> func Or_error.t
  val run_abi : Abi.func -> Abi.func Or_error.t
end

(** Uses the [Egraph] module to perform a variety of optimizations
    to a function, namely:

    - Instruction rewriting/simplification/canonicalization via rewrite rules
    - Global value numbering (GVN)
    - Global code motion (GCM)
    - Loop-invariant code motion (LICM)
    - Store-to-load forwarding
    - Redundant load elimination (RLE)
    - Resolving constant block parameters

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
    from the entry block.

    This transformation, among others, is also performed by [Simplify_cfg].
*)
module Remove_disjoint_blks : sig
  val run : func -> func
  val run_abi : Abi.func -> Abi.func
end

(** Runs a data-flow analysis to determine block arguments
    that are constant.

    This is also performed by [Egraph_opt], with additional information
    from global value numbering (GVN).

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

(** Performs the following control-flow transformations:

    - Merge all `ret` instructions to a single block
    - If-conversion
    - Straight-line block merging
    - Edge contraction/jump tunneling
    - Short-circuiting AND/OR simplification
    - Eliminate redundant conditional branches in empty blocks
    - Collapse simple `switch` instructions into branches
    - Tail-recursion elimination
    - Remove disjoint/unreachable blocks

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
