(** The typing environment.

    Maps variables and module symbols to their types. It is
    built by {!collect} as a linear pass over the IR.

    Well-formedness is validated separately by {!Typecheck}.
*)

open Core
open Regular.Std
open Virtual

(** The typing environment. *)
type t

(** Creates an empty environment for the given target. *)
val create : Target.t -> t

(** The target the environment was built for. *)
val target : t -> Target.t

(** {2 Queries} *)

(** The type associated with a data symbol.

    References to data symbols not defined in the module are allowed, as
    these can be resolved during linking.
*)
val typeof_data : string -> t -> Type.named option

(** The defined data symbols in the module. *)
val datanames : t -> string seq

(** The prototype associated with a function symbol.

    References to function symbols not defined in the module are allowed,
    as these can be resolved during linking.
*)
val typeof_fn : string -> t -> Type.proto option

(** The defined function symbols in the module. *)
val funcnames : t -> string seq

(** The compound type associated with a type name. *)
val typeof_typ : string -> t -> Type.named Or_error.t

(** The defined type names in the module. *)
val typenames : t -> string seq

(** The type of a variable in a given function. *)
val typeof_var : func -> Var.t -> t -> Type.t Or_error.t

(** [layout name env] returns the resolved layout of type [name], if it
    exists. *)
val layout : string -> t -> Type.layout Or_error.t

(** {2 Incremental construction}

    These register individual entities and are used by {!Typecheck} as it
    validates a module. Normal clients should use {!collect}.
*)

(** Registers a type definition. *)
val add_typ : Type.named -> t -> t Or_error.t

(** Registers a data symbol. *)
val add_data : Data.t -> t -> t Or_error.t

(** Registers a function prototype. *)
val add_fn : func -> t -> t Or_error.t

(** [add_var fn v ty env] registers variable [v] of function [fn] with type
    [ty], failing if [v] is already bound to an incompatible type. *)
val add_var : func -> Var.t -> Type.t -> t -> t Or_error.t

(** {2 Collection} *)

(** [collect m ~target] builds the environment for module [m] by collecting
    the types of all variables and symbols directly from the IR. *)
val collect : module_ -> target:Target.t -> t Or_error.t

(** [collect_fns env fns] refreshes the variable types of [fns] in [env],
    used to update the environment after a pass transforms functions. The
    module-level entities of [env] are left unchanged. *)
val collect_fns : t -> func list -> t Or_error.t
