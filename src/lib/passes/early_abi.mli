(** This pass runs several transformations on a given function
    according to the ABI specification of a target platform.

    Specifically:

    1. Function calls containing variadic arguments are expanded
    to correspond to either register or memory arguments.

    2. Function calls containing compound types as arguments are
    expanded to either register or memory arguments.

    3. Functions that accept compound types as arguments are
    expanded to either register or memory arguments.

    4. [vaarg] instructions are lowered to perform the necessary
    logic to manually access variadic arguments.

    The reason for doing these transformations at the [Virtual] IR
    level is to provide opportunities for middle-end optimizations
    wherever possible, as the transformations may insert or affect
    memory operations.

    Certain target-specific constructs (such as [vastart]) are not
    implemented in this pass, as they do not fit within the level of
    abstraction provided by the [Virtual] IR; they may require an
    explicit notion registers and stack frames. Such transformations
    are therefore delayed until the instruction selection phase of
    the compilation pipeline.
*)

open Virtual

val run : Typecheck.env -> func -> func Context.t
