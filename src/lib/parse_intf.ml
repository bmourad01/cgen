module type S = sig
  (** The data structure being parsed. *)
  type t

  (** Parse a raw string. *)
  val from_string : string -> t Context.t

  (** Parse a file by name. *)
  val from_file : string -> t Context.t

  (** Parse from stdin. *)
  val from_stdin : unit -> t Context.t
end
