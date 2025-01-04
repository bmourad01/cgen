(** Abstract interface for a compilation context. *)

open Core
open Monads.Std
open Regular.Std

module type S = sig
  (** The monadic context. *)
  type 'a t

  module Var : sig
    (** Generates a fresh program variable. *)
    val fresh : Var.t t
  end

  module Label : sig
    (** Generates a fresh program label. *)
    val fresh : Label.t t
  end

  (** Local state for the computation.

      This is not required to be persistent across runs of the context.
  *)
  module Local : sig
    (** [set k v] sets the value associated with key [k] to [v]. *)
    val set : 'a Dict.tag -> 'a -> unit t

    (** [get k] returns the value [Some v] associated with [k] if it
        exists, and [None] otherwise. *)
    val get : 'a Dict.tag -> 'a option t

    (** [get' k ~default] returns the value associated with [k] if it exists,
        and [default] otherwise. *)
    val get' : 'a Dict.tag -> default:'a -> 'a t

    (** [get_err k] returns the value associated with [k] if it exists,
        and terminates the computation with an error otherwise. *)
    val get_err : 'a Dict.tag -> 'a t

    (** [erase k] removes [k] from the local state. This can be useful to
        reset the state for re-runs or to discard state that is isolated to
        a particular analysis or transformation. *)
    val erase : 'a Dict.tag -> unit t
  end

  (** Lifts an [Or_error] computation into the context.

      If it is [Ok x], then [x] is returned, otherwise the computation fails
      with the error.
  *)
  val lift_err : 'a Or_error.t -> 'a t

  (** Terminates the computation with an error. *)
  val fail : Error.t -> 'a t

  (** Same as [fail], but formats a pretty-printed error message. *)
  val failf : ('a, Format.formatter, unit, unit -> 'b t) format4 -> 'a

  (** [when_ k f] evaluates [f] if [k] is [true]. *)
  val when_ : bool -> (unit -> unit t) -> unit t

  (** [unless k f] evaluates [f] if [k] is [false]. *)
  val unless : bool -> (unit -> unit t) -> unit t

  module Syntax : sig
    include Monad.Syntax.S with type 'a t := 'a t
    include Monad.Syntax.Let.S with type 'a t := 'a t

    (** Attempts to unwrap an [Or_error] computation into the context, and
        fails if it is an error. *)
    val (>>?) : 'a Or_error.t -> ('a -> 'b t) -> 'b t

    (** Same as the [(>>?)] infix notation. *)
    val (let*?) : 'a Or_error.t -> ('a -> 'b t) -> 'b t
  end

  include Monad.S
    with type 'a t := 'a t
     and module Syntax := Syntax

  (** Same as [List.map], but [f] is allowed to fail early. In this case,
      the error is lifted into the context. *)
  val map_list_err : 'a list -> f:('a -> 'b Or_error.t) -> 'b list t

  (** Same as [List.iter], but [f] is allowed to fail early. In this case,
      the error is lifted into the context. *)
  val iter_list_err : 'a list -> f:('a -> unit Or_error.t) -> unit t

  (** Same as [Seq.map], but [f] is allowed to fail early. In this case,
      the error is lifted into the context. *)
  val map_seq_err : 'a seq -> f:('a -> 'b Or_error.t) -> 'b seq t

  (** Same as [Seq.iter], but [f] is allowed to fail early. In this case,
      the error is lifted into the context. *)
  val iter_seq_err : 'a seq -> f:('a -> unit Or_error.t) -> unit t
end
