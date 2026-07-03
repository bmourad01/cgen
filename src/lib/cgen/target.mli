(** A descriptor of a compilation target. *)

open Regular.Std

type t

(** Enumerates all of the declared targets. *)
val enum_targets : unit -> t seq

(** Declares a target descriptor.

    [name]: the name of the target. This is used to
    uniquely identify the target.

    [little]: if [true], the target is little-endian.

    [data_model]: the C data model, which also fixes the native
    word/pointer size.

    Raises [Failure] if a target with [name] was already
    declared.
*)
val declare :
  name:string ->
  little:bool ->
  data_model:Cgen_utils.C_data_model.t ->
  unit ->
  t

(** Searches a declared target by name. *)
val find : string -> t option

(** The name of the target. *)
val name : t -> string

(** The type of the native word/pointer size of the target (derived
    from the data model). *)
val word : t -> Type.imm_base

(** The native bit-width of the target. *)
val bits : t -> int

(** Returns [true] if the target is little-endian. *)
val little : t -> bool

(** The C data model of the target. *)
val data_model : t -> Cgen_utils.C_data_model.t

include Regular.S with type t := t
