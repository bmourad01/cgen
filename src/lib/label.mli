(** A generic program label.

    The scope of each label is limited to the body of a function.

    Globally-scoped locations, or {b symbols} in our parlance, should
    be referred to by name.
*)

open Graphlib.Std
open Regular.Std

(** A program label. *)
type t

(** The pseudo-entry label. Primarily useful for computing the
    dominator tree of a graph .*)
val pseudoentry : t

(** The pseudo-exit label. Primarily useful for computing the
    dominator tree of a graph .*)
val pseudoexit : t

(** Returns [true] if the label is [pseudoentry] or [pseudoexit]. *)
val is_pseudo : t -> bool

include Regular.S with type t := t

(** A specialized tree data structure for labels, implemented
    as a PATRICIA tree. *)
module Tree : Patricia_tree_intf.S with type key := t

(** The signature for graphs with labels as nodes. *)
module type Graph = Graph
  with type node = t
   and type Edge.label = unit

(** An interface for connecting entry and exit nodes of the graph
    with [pseudoentry] and [pseudoexit], respectively. *)
module Pseudo(G : Graph) : sig
  val add : G.t -> G.t
end
