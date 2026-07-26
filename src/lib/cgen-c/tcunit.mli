(** A typed (elaborated) translation unit.

    The top-level result of elaborating a parsed [Cunit.t]: the
    typed declarations and the {!Type_env.t} that carries both the
    typing environment used to resolve all tag and identifier
    references and the precomputed layout maps for downstream
    consumers (codegen, sizeof, offsetof, etc.).
*)

open Core

(** A typed translation unit. *)
type t [@@deriving bin_io, compare, equal, hash, sexp]

(** [create ~decls ~layout] builds a typed translation unit. *)
val create :
  decls:Tdecl.t list ->
  layout:Type_env.t ->
  t

(** The unit's top-level declarations, in source order. *)
val decls : t -> Tdecl.t list

(** The unit's typing environment (carrying both the name/type bindings and
    the precomputed layout maps). *)
val layout : t -> Type_env.t

(** The typing environment used to elaborate the unit. Same as {!layout}. *)
val tenv : t -> Type_env.t

(** The data model under which the unit was elaborated. Equivalent
    to [Type_env.dmodel (layout u)]. *)
val dmodel : t -> Data_model.t

(** {1 Pretty printer} *)

(** Renders the unit in C syntax: each declaration in order,
    separated by a blank line. *)
val pp : Format.formatter -> t -> unit

(** [to_string u] is [pp] rendered to a string. *)
val to_string : t -> string
