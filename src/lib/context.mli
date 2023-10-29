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

(** Terminates the computation with an error. *)
val fail : Error.t -> 'a t

(** Same as [fail], but formats a pretty-printed error message. *)
val failf : ('a, Format.formatter, unit, unit -> 'b t) format4 -> 'a

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
  (** [insn d ?dict] returns a data instruction [d] with a fresh label. *)
  val insn : ?dict:Dict.t -> Virtual.Insn.op -> Virtual.insn t

  (** [blk ?dict ?args ?insns ~ctrl ()] returns a block with [dict],
      [args], [insns], and [ctrl], while generating a fresh label for
      the block. *)
  val blk :
    ?dict:Dict.t ->
    ?args:var list ->
    ?insns:Virtual.insn list ->
    ctrl:Virtual.ctrl ->
    unit ->
    Virtual.blk t

  (** Same as [blk], but also generates fresh labels for the [insns].
      Allows a pre-existing label for the block. *)
  val blk' :
    ?dict:Dict.t ->
    ?label:label option ->
    ?args:var list ->
    ?insns:Virtual.Insn.op list ->
    ctrl:Virtual.ctrl ->
    unit ->
    Virtual.blk t

  module Module : sig
    (** Same as [Virtual.Module.map_funs], but [f] is a context
        computation. *)
    val map_funs :
      Virtual.module_ ->
      f:(Virtual.func -> Virtual.func t) ->
      Virtual.module_ t
  end
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
