(** The compilation context. *)

open Core
open Regular.Std

(** The state for the compilation context. *)
module State : sig
  type t
  include Regular.S with type t := t
end

type state = State.t

(** The compilation context. *)
type 'a t

(** Returns the current target descriptor. *)
val target : Target.t t

(** [register_machine m] registers the machine implementation [m].

    The machine is registered by its provided target (see the [Target]
    module).

    @raise Invalid_argument if [m] is already registered.
*)
val register_machine : (module Machine_intf.S) -> unit

(** Returns the target machine implementation for the current context. *)
val machine : (module Machine_intf.S) t

(** Initializes the state. *)
val init : Target.t -> state

(** [run x s] runs the computation [x] with the initial state [s],
    and returns the result of computing [x] with the updated state,
    or an error if the computation failed. *)
val run : 'a t -> state -> ('a * state) Or_error.t

(** [eval x s] is the same as [run x s], except the updated state is
    discarded when [x] terminates. *)
val eval : 'a t -> state -> 'a Or_error.t

include Context_intf.S_virtual with type 'a t := 'a t
