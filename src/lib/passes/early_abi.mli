(** This pass runs several transformations on each function in
    a given module according to the ABI of the target platform.

    Specifically:

    1. Functions that accept compound types as arguments are
    lowered to accept basic types.

    2. Function calls that pass compound types as arguments are
    lowered to pass basic types.

    3. [vaarg] instructions are lowered to perform the necessary
    logic to manually access variadic arguments.

    The reason for doing these transformations at the [Virtual] IR
    level is to provide more opportunity for middle-end optimizations,
    where possible.

    Certain target-specific constructs (such as [vastart]) are not
    implemented in this pass, as they do not fit within the level of
    abstraction provided by the [Virtual] IR; they may require a notion
    of explicit registers and stack frames. Such transformations are
    therefore delayed until the instruction selection phase of the
    compilation pipeline.    
*)

open Virtual

val run : Typecheck.env -> module_ -> module_ Context.t
