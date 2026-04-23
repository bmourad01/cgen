open Core
open Regular.Std

module type Pre = sig
  type local

  (** A switch table. *)
  module Table : sig
    type t [@@deriving bin_io, compare, equal, sexp]

    (** Creates a switch table from an association list.

        @raise Invalid_argument if the list has duplicate keys.
    *)
    val create_exn : (Bv.t * local) list -> Type.imm -> t

    (** Same as [create_exn], but returns an error upon failure. *)
    val create : (Bv.t * local) list -> Type.imm -> t Or_error.t

    (** Returns the elements of the table. *)
    val enum : t -> (Bv.t * local) seq

    (** Returns the number of cases in the table. *)
    val length : t -> int

    (** Returns the immediate type for the index into the table. *)
    val typ : t -> Type.imm

    (** [find t v] searches the table [t] for the label associated
        with the constant [v]. *)
    val find : t -> Bv.t -> local option

    (** [map_exn t ~f] applies [f] to each element of [t].

        @raise Invalid_argument if [f] produces a duplicate key.
    *)
    val map_exn : t -> f:(Bv.t -> local -> Bv.t * local) -> t

    (** Returns the set of free variables in the table. *)
    val free_vars : t -> Var.Tree_set.t

    (** Same as [map_exn], but returns [Error _] if [f] produces a
        duplicate key. *)
    val map : t -> f:(Bv.t -> local -> Bv.t * local) -> t Or_error.t
  end

  type table = Table.t [@@deriving bin_io, compare, equal, sexp]

  (** A valid index into the switch table.

      The [`sym (s, offset)] constructor is included because it is
      technically legal to use a symbol as an index into the table.
      A constant propagation pass could resolve the index to some
      symbol, although this is rarely a case.
  *)
  type swindex = [
    | `var of Var.t
    | `sym of string * int
  ] [@@deriving bin_io, compare, equal, sexp]

  val pp_swindex : Format.formatter -> swindex -> unit
end

module type S = sig
  type t

  (** Returns the set of free variables in the control-flow instruction. *)
  val free_vars : t -> Var.Tree_set.t

  (** Pretty-prints a control-flow instruction. *)
  val pp : Format.formatter -> t -> unit
end
