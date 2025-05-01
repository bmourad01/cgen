(** Interface for parsers. *)

open Parse_intf

(** The parser for Virtual programs. *)
module Virtual : S with type t := Virtual.module_
