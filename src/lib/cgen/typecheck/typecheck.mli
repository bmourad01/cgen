(** Checks a module for well-formedness.

    The typing environment consumed by the rest of the pipeline is built
    separately by {!Type_env}. This pass will independently build such
    an environment, and use it to validate the module.
*)

open Core
open Virtual

(** Type checks a module, parameterized by the target. Returns an error
    if the module is not well-formed. *)
val check : module_ -> target:Target.t -> unit Or_error.t
