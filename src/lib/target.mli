(** A descriptor of a compilation target. *)

open Regular.Std

type t

(** Enumerates all of the declared targets. *)
val enum_targets : unit -> t seq

(** Declares a target descriptor.

    [name]: the name of the target. This is used to
    uniquely identify the target.

    [word]: the type for the word size of the target.

    [little]: if [true], the target is little-endian.

    @raise Failure if a target with [name] was already
    declared.
*)
val declare :
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

include Regular.S with type t := t
