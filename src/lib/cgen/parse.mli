(** Interface for parsers. *)

open Parse_intf

(** The parser for Virtual programs. *)
module Virtual : S with type t := Virtual.module_

(** The parser for Structured programs. *)
module Structured : S with type t := Structured.module_
