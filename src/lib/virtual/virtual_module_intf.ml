open Core
open Regular.Std

module type S = sig
  type data
  type func
  type t [@@deriving bin_io, compare, equal, sexp]

  (** The name of the module. *)
  val name : t -> string

  (** Structs defined in the module. *)
  val data : ?rev:bool -> t -> data seq

  (** Functions defined in the module. *)
  val funs : ?rev:bool -> t -> func seq

  (** Returns the dictionary of the module. *)
  val dict : t -> Dict.t

  (** Replaces the dictionary of the module. *)
  val with_dict : t -> Dict.t -> t

  (** [with_tag m t v] binds [v] to tag [t] in the dictionary of [m]. *)
  val with_tag : t -> 'a Dict.tag -> 'a -> t

  (** Returns [true] if the module has the associated name. *)
  val has_name : t -> string -> bool

  (** Appends a struct to the module. *)
  val insert_data : t -> data -> t

  (** Appends a function to the module. *)
  val insert_fn : t -> func -> t

  (** Removes the struct associated with the name. *)
  val remove_data : t -> string -> t

  (** Removes the function associated with the name. *)
  val remove_fn : t -> string -> t

  (** Returns the module with each struct transformed by [f]. *)
  val map_data : t -> f:(data -> data) -> t

  (** Returns the module with each function transformed by [f]. *)
  val map_funs : t -> f:(func -> func) -> t

  (** Replaces the functions in the module. *)
  val with_funs : t -> func list -> t

  (** Returns the module with each struct transformed by [f],
      where [f] may fail. *)
  val map_data_err : t -> f:(data -> data Or_error.t) -> t Or_error.t

  (** Returns the module with each function transformed by [f],
      where [f] may fail. *)
  val map_funs_err : t -> f:(func -> func Or_error.t) -> t Or_error.t

  include Regular.S with type t := t
end
