(** Type-safe keys for {!Hdict}, adapted from BAP's Knowledge Base. *)

open Hdict_key_intf

(** Create a namespace for registering keys. *)
module Make(Name : Name) : S with type name := Name.t
