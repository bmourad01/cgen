module type S = sig
  (** The data structure being parsed. *)
  type t

  (** Parse a raw string. *)
  val from_string : string -> t Context.t

  (** Parse a file by name. *)
  val from_file : string -> t Context.t
end
