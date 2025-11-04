(** Performs SROA (Scalar Replacement of Aggregates).

    This pass aims to analyze the usage of slots in a function, where
    individual fields of the slot can be separated into their own
    unique slots themselves.

    This is typical when a slot is allocated to hold a structure and
    pointer arithmetic is used to store to and load from individual
    fields of this structure. If these fields can become their own slots,
    then they can possibly promoted to SSA variables, enabling more
    optimization opportunities.

    The function must be in SSA form for this pass.
*)

open Virtual

val run : func -> func Context.t
