open Core
open Hashmap_intf

module Make(K : Hashtbl.Key) : S with type key := K.t
