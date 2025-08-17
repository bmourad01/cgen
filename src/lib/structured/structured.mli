open Regular.Std

(** A statement. *)
module Stmt : sig
  (** A statement includes:

      - Normal operations
      - [`nop]: no-op (does nothing)
      - [`seq (a, b)]: executes the statement [a], then [b]
      - [`ite (c, y, n)]: if the condition [c] is true, then [y] is executed,
        otherwise [n] is executed
      - [`while_ (c, b)]: while the condition [c] is true, [b] is executed
      - [`dowhile (b, c)]: [b] is executed until [c] is not true; note that [b]
        will always execute at least once
      - [`sw (i, ty, cs)]: based on the index [i] of type [ty], branch to the case
        in [cs] where [i] is equal to the key, and execute the body
      - [`label l]: marks a label [l] as a target for a [goto]
      - [`goto l]: jumps to a label [l]
      - [`hlt]: halts execution of the program
      - [`ret x]: return from the function, with an optional value [x]
  *)
  type t = [
    | Virtual.Insn.op
    | `nop
    | `seq of t * t
    | `ite of Var.t * t * t
    | `while_ of Var.t * t
    | `dowhile of t * Var.t
    | `sw of Var.t * Type.imm * (Bv.t * t) list
    | `label of Label.t
    | `goto of Label.t
    | `hlt
    | `ret of Virtual.operand option
  ] [@@deriving bin_io, compare, equal, sexp]

  val pp : Format.formatter -> t -> unit
end

type stmt = Stmt.t [@@deriving bin_io, compare, equal, sexp]
type slot = Virtual.Slot.t [@@deriving bin_io, compare, equal, sexp]

module Func : sig
  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a function. *)
  val create :
    ?dict:Dict.t ->
    ?slots:slot list ->
    name:string ->
    body:stmt ->
    args:(Var.t * Type.arg) list ->
    unit ->
    t

  (** Returns the name of the function. *)
  val name : t -> string

  (** Returns the slots of the function. *)
  val slots : ?rev:bool -> t -> slot seq

  (** Returns the body of the function. *)
  val body : t -> stmt

  (** Returns the arguments of the function, along with their types. *)
  val args : ?rev:bool -> t -> (Var.t * Type.arg) seq

  (** Returns the dictionary of the function. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the function. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag fn t v] binds [v] to tag [t] in the dictionary of [fn]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Replaces the body of the function. *)
  val with_body : t -> stmt -> t

  (** Returns [true] if the function has the associated name. *)
  val has_name : t -> string -> bool

  (** Transforms the body of the function. *)
  val map_body : t -> f:(stmt -> stmt) -> t

  (** Appends a slot to the function. *)
  val insert_slot : t -> slot -> t

  (** Removes a slot from the function that corresponds to the given var. *)
  val remove_slot : t -> Var.t -> t

  (** [prepend_arg ?before fn x t] adds the argument [x] of type [t] to [fn].

      If [before] is [None], then [x] is inserted at the beginning of the
      argument list.

      If [before] is [Some y], then [x] will appear directly before the
      argument [y]. If [y] doesn't exist, then [x] is not inserted.
  *)
  val prepend_arg : ?before:Var.t -> t -> Var.t -> Type.arg -> t

  (** [append_arg ?after fn x t] adds the argument [x] of type [t] to [fn].

      If [after] is [None], then [x] is inserted at the end of the
      argument list.

      If [after] is [Some y], then [x] will appear directly after the
      argument [y]. If [y] doesn't exist, then [x] is not inserted.
  *)
  val append_arg : ?after:Var.t -> t -> Var.t -> Type.arg -> t

  (** [remove_arg fn x] removes the argument [x] from [fn], if it exists. *)
  val remove_arg : t -> Var.t -> t

  include Regular.S with type t := t
end
