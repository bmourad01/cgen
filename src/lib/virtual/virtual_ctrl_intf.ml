open Core
open Regular.Std

module type S = sig
  type operand
  type local
  type dst
  type ret

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
    val free_vars : t -> Var.Set.t

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

  (** A control-flow instruction.

      [`hlt] terminates execution of the program. This is typically used
      to mark certain program locations as unreachable.

      [`jmp dst] is an unconditional jump to the destination [dst].

      [`br (cond, yes, no)] evaluates [cond] and jumps to [yes] if it
      is non-zero. Otherwise, the destination is [no].

      [`ret x] returns from a function. If the function returns a value,
      then [x] holds the value (and must not be [None]).

      [`sw (typ, index, default, table)] implements a jump table.
      For a variable [index] of type [typ], it will find the associated
      label of [index] in [table] and jump to it, if it exists. If not,
      then the destination of the jump is [default].
  *)
  type t = [
    | `hlt
    | `jmp of dst
    | `br  of Var.t * dst * dst
    | `ret of ret
    | `sw  of Type.imm * swindex * local * table
  ] [@@deriving bin_io, compare, equal, sexp]

  (** Returns the set of free variables in the control-flow instruction. *)
  val free_vars : t -> Var.Set.t

  (** Pretty-prints a control-flow instruction. *)
  val pp : Format.formatter -> t -> unit
end
