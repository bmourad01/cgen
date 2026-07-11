(** Support for C-style linkage of symbols. *)


(** Linkage metadata. *)
type t

(** ELF-shaped symbol visibility. *)
type visibility =
  | Default
  | Hidden
  | Internal
  | Protected
[@@deriving bin_io, compare, equal, hash, sexp]

(** Creates the linkage. [weak] defaults to [false] and [visibility] to
    [Default]. *)
val create :
  ?section:string option ->
  ?weak:bool ->
  ?visibility:visibility ->
  export:bool ->
  unit ->
  t

(** The name of the section for a symbol to be linked in. *)
val section : t -> string option

(** Returns [true] if the symbol is visible to external compilation
    units. *)
val export : t -> bool

(** Returns [true] if the symbol is weak (a [__attribute__((weak))] or
    weak definition that a strong one overrides). *)
val weak : t -> bool

(** The symbol's ELF visibility. *)
val visibility : t -> visibility

(** The default linkage for an exported symbol. *)
val default_export : t

(** The default linkage for a static symbol. *)
val default_static : t

include Cgen_utils.Regular.S with type t := t
