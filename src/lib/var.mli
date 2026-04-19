(** A program variable. *)

open Base
open Regular.Std

(** A program variable. *)
type t = private Int63.t

include Regular.S with type t := t

(** PATRICIA tree-base map over variables. More efficient than
    the [Regular.S]-derived [Map] for most uses. *)
module Tree : Patricia_tree_intf.S with type key := t

(** PATRICIA tree-based set of variables. More efficient than
    the [Regular.S]-derived [Set] for most uses. *)
module Tree_set : Patricia_tree_intf.Set with type key := t

(** An open-addressing hash table keyed by variables. *)
module Dense_table : Dense_intf.Map with type key := t

(** An open-addressing hash set of variables. *)
module Dense_set : Dense_intf.Set with type key := t
