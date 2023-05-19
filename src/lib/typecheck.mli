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

      This is because the environment itself is needed by the
      SSA transformation (for computing the types of block
      arguments). Afterwards, the environment may be reused.
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
