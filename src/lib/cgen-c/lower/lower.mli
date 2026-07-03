(** Lowering a typed C translation unit ([Tcunit.t]) to Structured IR.

    The result is handed to the backend ([Passes.destructure] and the rest
    of the pipeline) to produce native code. Locals and parameters become
    stack slots; the optimizer promotes scalar slots back into registers.

    Unsupported constructs (variadics, bitfields, compound literals,
    aggregate global initializers, switch) raise via the context monad's
    error.
*)

(** [module_ ~name tc] lowers [tc] into a Structured IR module, allocating
    fresh variables and labels in the context monad. [name] becomes the
    module name. *)
val module_ : name:string -> Tcunit.t -> Cgen.Structured.module_ Cgen.Context.t
