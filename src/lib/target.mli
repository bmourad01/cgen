(** A compilation target. *)

open Regular.Std

type t

(** Creates a target. *)
val create :
  name:string ->
  bits:int ->
  unit ->
  t

(** The name of the target. *)
val name : t -> string

(** The native bit-width of the target. *)
val bits : t -> int

include Regular.S  with type t := t
