(** Checks a module for well-formedness and builds a typing
    environment. *)

open Core
open Virtual

(** The typing environment. *)
module Env : sig
  type t

  (** The target used during type checking. *)
  val target : t -> Target.t

  (** The type associated with a data symbol.

      Note that references to data symbols not defined in a
      module are allowed, as these can be resolved during
      linking.
  *)
  val typeof_data : string -> t -> Type.compound option

  (** The prototype associated with a function symbol.

      Note that references to function symbols not defined
      in a module are allowed, as these can be resolved during
      linking.
  *)
  val typeof_fn : string -> t -> Type.proto option

  (** The compound type associated with a type name. *)
  val typeof_typ : string -> t -> Type.compound Or_error.t

  (** The type of a variable in a given function. Note that the
      result of [Var.base] is used to look up the variable in
      the environment.

      This is to ensure compatibility of the environment before
      and after SSA renaming of variables, thus avoiding the
      need to run the type-checking algorithm again.
  *)
  val typeof_var : func -> Var.t -> t -> Type.t Or_error.t

  (** [layout name env] returns the resolved layout of type [name],
      if it exists. *)
  val layout : string -> t -> Type.layout Or_error.t
end

type env = Env.t

(** Type checks a module, parameterized by the target. If
    successful, the typing environment is returned. *)
val run : module_ -> target:Target.t -> env Or_error.t

(** [update_fn env fn] updates [env] with [fn].

    If [fn] already exists in [env], the contents of the
    previous version are overwritten. Otherwise, [env] is
    extended with the details of [fn].
*)
val update_fn : env -> func -> env Or_error.t

(** Same as [update_fn], but operates over a list of functions.

    This can be used to update a batch of functions, or when
    an update to a function's signature requires changes to
    its callers in the same module.
*)
val update_fns : env -> func list -> env Or_error.t
