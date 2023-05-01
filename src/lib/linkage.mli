(** Support for C-style linkage of symbols. *)

open Regular.Std

(** Linkage metadata. *)
type t

(** Creates the linkage. *)
val create : ?section:string option -> export:bool -> unit -> t

(** The name of the section for a symbol to be linked in. *)
val section : t -> string option

(** Returns [true] if the symbol is visible to external compilation
    units. *)
val export : t -> bool

(** The default linkage for an exported symbol. *)
val default_export : t

(** The default linkage for a static symbol. *)
val default_static : t

include Regular.S with type t := t
