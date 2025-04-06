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

(** The target-specific implementation needed for the compilation pipeline. *)
module type Machine = Context_machine_intf.S
  with type 'a context := 'a t

(** [register_machine t m] registers the machine implementation [m] for
    target descriptor [t].

    @raise Invalid_argument if [t] is already registered with a machine.
*)
val register_machine : Target.t -> (module Machine) -> unit

(** Forces all of the machines to register. *)
val init_machines : unit -> unit

(** Returns the target machine implementation for the current context. *)
val machine : (module Machine) t

(** Helpers for generating [Virtual] terms. *)
module Virtual : Context_virtual_intf.S
  with type var := Var.t
   and type label := Label.t
   and type 'a context := 'a t

(** Initializes the state. *)
val init : Target.t -> state

(** [run x s] runs the computation [x] with the initial state [s],
    and returns the result of computing [x] with the updated state,
    or an error if the computation failed. *)
val run : 'a t -> state -> ('a * state) Or_error.t

(** [eval x s] is the same as [run x s], except the updated state is
    discarded when [x] terminates. *)
val eval : 'a t -> state -> 'a Or_error.t

include Context_intf.S with type 'a t := 'a t
