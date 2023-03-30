(** A compilation target. *)

open Regular.Std

type t

(** Creates a target.

    [name]: the name of the target.

    [word]: the type for the word size of the target.

    [little]: if [true], the target is little-endian.
*)
val create :
  name:string ->
  word:Type.imm_base ->
  little:bool ->
  unit ->
  t

(** The name of the target. *)
val name : t -> string

(** The type of the native word size of the target. *)
val word : t -> Type.imm_base

(** The native bit-width of the target. *)
val bits : t -> int

(** Returns [true] if the target is little-endian. *)
val little : t -> bool

include Regular.S  with type t := t
