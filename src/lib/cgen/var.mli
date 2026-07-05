(** A program variable. *)

open Base
open Cgen_containers

(** A program variable. *)
type t = private int

(** Escape hatch for constructing a variable via its underlying
    representation. *)
val of_int_unsafe : int -> t

include Cgen_utils.Regular.S with type t := t

(** PATRICIA tree-base map over variables. More efficient than
    the [Cgen_utils.Regular.S]-derived [Map] for most uses. *)
module Tree : Patricia_tree_intf.S with type key := t

(** PATRICIA tree-based set of variables. More efficient than
    the [Cgen_utils.Regular.S]-derived [Set] for most uses. *)
module Tree_set : Patricia_tree_intf.Set
  with type key := t
   and type 'a map := 'a Tree.t

(** An open-addressing hash table keyed by variables. *)
module Dense_table : Dense_intf.Map with type key := t

(** An open-addressing hash set of variables. *)
module Dense_set : Dense_intf.Set with type key := t
