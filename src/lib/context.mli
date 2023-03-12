(** The compilation context.

    All elements of the compilation pipeline are expected to be
    parameterized by this context. It contains various book keeping
    and state.
*)

open Core
open Monads.Std
open Regular.Std

(** The state for the compilation context. *)
module State : sig
  type t

  include Regular.S with type t := t
end

type state = State.t

(** The compilation context. *)
type 'a t

val return : 'a -> 'a t
val bind : 'a t -> f:('a -> 'b t) -> 'b t
val map : 'a t -> f:('a -> 'b) -> 'b t

(** Terminates the computation with an error. *)
val fail : Error.t -> 'a t

(** Lifts an [Or_error] computation into the context.

    If it is [Ok x], then [x] is returned, otherwise the computation fails
    with the error.
*)
val lift_err : 'a Or_error.t -> 'a t

(** Returns the target machine. *)
val target : Target.t t

type var = Var.t

module Var : sig
  (** Generates a fresh temporary variable. *)
  val fresh : var t
end

type label = Label.t

module Label : sig
  (** Generates a fresh program label. *)
  val fresh : label t
end

module Virtual : sig
  module Insn : sig
    (** [data d] returns a data instruction [d] with a fresh label. *)
    val data : Virtual.Insn.Data.op -> Virtual.Insn.data t
  end

  (** [blk ?phi ?data ~ctrl ()] returns a block with the instructions
      [phi], [data], and [ctrl], while generating a fresh label for the
      block. *)
  val blk :
    ?args:(var * Virtual.Blk.arg_typ) list ->
    ?data:Virtual.Insn.data list ->
    ctrl:Virtual.Insn.ctrl ->
    unit ->
    Virtual.blk t

  (** Same as [blk], but also generates fresh labels for the instructions.
      Allows a pre-existing label for the block. *)
  val blk' :
    ?label:label option ->
    ?args:(var * Virtual.Blk.arg_typ) list ->
    ?data:Virtual.Insn.Data.op list ->
    ctrl:Virtual.Insn.ctrl ->
    unit ->
    Virtual.blk t
end

(** Initializes the state. *)
val init : Target.t -> state

(** [run x s] runs the computation [x] with the initial state [s],
    and returns the result of computing [x] with the updated state,
    or an error if the computation failed. *)
val run : 'a t -> state -> ('a * state) Or_error.t

(** [eval x s] is the same as [run x s], except the updated state is
    discarded when [x] terminates. *)
val eval : 'a t -> state -> 'a Or_error.t

module Syntax : sig
  include Monad.Syntax.S with type 'a t := 'a t
  include Monad.Syntax.Let.S with type 'a t := 'a t

  (** Attempts to unwrap an [Or_error] computation into the context, and
      fails if it is an error. *)
  val (>>?) : 'a Or_error.t -> ('a -> 'b t) -> 'b t

  (** Same as the [(>>?)] infix notation. *)
  val (let*?) : 'a Or_error.t -> ('a -> 'b t) -> 'b t
end

include Monad.S with type 'a t := 'a t and module Syntax := Syntax
