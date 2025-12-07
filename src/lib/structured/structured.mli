open Core
open Regular.Std

(** A statement. *)
module Stmt : sig
  (** A statement includes:

      - Normal operations (see [Virtual.Insn])
      - [`nop]: no-op (does nothing)
      - [`break]: exit the current loop or switch statement
      - [`continue]: skip to the next iteration of the current loop
      - [`seq (a, b)]: executes the statement [a], then [b]
      - [`ite (c, y, n)]: if the condition [c] is true, then [y] is executed,
        otherwise [n] is executed
      - [`when_ (c, b)]: equivalent to [`ite (c, b, `nop)]
      - [`unless (c, b)]: equivalent to [`ife (c, `nop, b)]
      - [`loop b]: execute [b] in a loop with no head or tail guard; equivalent
        to a [while (1) { ... }] in C
      - [`while_ (c, b)]: while the condition [c] is true, [b] is executed
      - [`dowhile (b, c)]: [b] is executed until [c] is not true; note that [b]
        will always execute at least once
      - [`sw (i, ty, cs)]: based on the index [i] of type [ty], branch to the
        matching case in [cs]
      - [`label (l, args)]: marks a label [l] as a target for a [goto], with
        arguments [args].
      - [`goto d]: jumps to a destination [d]
      - [`hlt]: halts execution of the program
      - [`ret x]: return from the function, with an optional value [x]
  *)
  type t = [
    | Virtual.Insn.op
    | `nop
    | `seq of t * t
    | `ite of Var.t * t * t
    | `when_ of Var.t * t
    | `unless of Var.t * t
    | `loop of t
    | `while_ of Var.t * t
    | `dowhile of t * Var.t
    | `break
    | `continue
    | `sw of Var.t * Type.imm * swcase list
    | `label of Label.t * Var.t list * t
    | `goto of Virtual.dst
    | `hlt
    | `ret of Virtual.operand option
  ] [@@deriving bin_io, compare, equal, sexp]

  (** A case for a [sw] (switch) statement.

      - [`case (i, b)]: execute [b] if the index matches [i]
      - [`default d]: execude [d] if the index does not match
        any other case
  *)
  and swcase = [
    | `case of Bv.t * t
    | `default of t
  ] [@@deriving bin_io, compare, equal, sexp]

  val pp : Format.formatter -> t -> unit
  val pp_swcase : Type.imm -> Format.formatter -> swcase -> unit
end

type stmt = Stmt.t [@@deriving bin_io, compare, equal, sexp]
type slot = Virtual.Slot.t [@@deriving bin_io, compare, equal, sexp]

module Func : sig
  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a function.

      [start] is the label of the function's entry point, and [body]
      is the actual function body. Thus, the function implicitly takes
      the form of [`label (start, [], body)].
  *)
  val create :
    ?dict:Dict.t ->
    ?slots:slot list ->
    name:string ->
    start:Label.t ->
    body:stmt ->
    args:(Var.t * Type.arg) list ->
    unit ->
    t

  (** Returns the name of the function. *)
  val name : t -> string

  (** The label of the function's entry point. *)
  val start : t -> Label.t

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

type func = Func.t [@@deriving bin_io, compare, equal, sexp]

module Module : sig
  type t [@@deriving bin_io, compare, equal, sexp]

  (** Creates a module. *)
  val create :
    ?dict:Dict.t ->
    ?typs:Type.compound list ->
    ?data:Virtual.data list ->
    ?funs:func list ->
    name:string ->
    unit ->
    t

  (** The name of the module. *)
  val name : t -> string

  (** Declared (compound) types that are visible in the module. *)
  val typs : ?rev:bool -> t -> Type.compound seq

  (** Structs defined in the module. *)
  val data : ?rev:bool -> t -> Virtual.data seq

  (** Functions defined in the module. *)
  val funs : ?rev:bool -> t -> func seq

  (** Returns the dictionary of the module. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the module. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag m t v] binds [v] to tag [t] in the dictionary of [m]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the module has the associated name. *)
  val has_name : t -> string -> bool

  (** Appends a type to the module. *)
  val insert_type : t -> Type.compound -> t

  (** Appends a struct to the module. *)
  val insert_data : t -> Virtual.data -> t

  (** Appends a function to the module. *)
  val insert_fn : t -> func -> t

  (** Removes the type associated with the name. *)
  val remove_type : t -> string -> t

  (** Removes the struct associated with the name. *)
  val remove_data : t -> string -> t

  (** Removes the function associated with the name. *)
  val remove_fn : t -> string -> t

  (** Returns the module with each struct transformed by [f]. *)
  val map_data : t -> f:(Virtual.data -> Virtual.data) -> t

  (** Returns the module with each function transformed by [f]. *)
  val map_funs : t -> f:(func -> func) -> t

  (** Returns the module with each type transformed by [f]. *)
  val map_typs : t -> f:(Type.compound -> Type.compound) -> t

  (** Replaces the functions in the module. *)
  val with_funs : t -> func list -> t

  (** Returns the module with each type transformed by [f],
      where [f] may fail. *)
  val map_typs_err :
    t -> f:(Type.compound -> Type.compound Or_error.t) -> t Or_error.t

  (** Returns the module with each struct transformed by [f],
      where [f] may fail. *)
  val map_data_err : t -> f:(Virtual.data -> Virtual.data Or_error.t) -> t Or_error.t

  (** Returns the module with each function transformed by [f],
      where [f] may fail. *)
  val map_funs_err : t -> f:(func -> func Or_error.t) -> t Or_error.t

  include Regular.S with type t := t
end

type module_ = Module.t [@@deriving bin_io, compare, equal, sexp]
