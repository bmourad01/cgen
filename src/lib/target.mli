(** A compilation target. *)

open Regular.Std

type t

(** Creates a target. *)
val create :
  name:string ->
  word:Type.imm_base ->
  unit ->
  t

(** The name of the target. *)
val name : t -> string

(** The type of the native word size of the target. *)
val word : t -> Type.imm_base

(** The native bit-width of the target. *)
val bits : t -> int

include Regular.S  with type t := t
