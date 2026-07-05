(** A generic program label.

    The scope of each label is limited to the body of a function.

    Globally-scoped locations, or {b symbols} in our parlance, should
    be referred to by name.
*)

open Core
open Cgen_containers

(** A program label. *)
type t = private int

(** An alias for {!t}, used where [t] would be shadowed (e.g. as the node type
    of {!Graph}). *)
type label = t

(** Escape hatch for constructing a label via its underlying
    representation. *)
val of_int_unsafe : int -> t

(** The pseudo-entry label. Primarily useful for computing the
    dominator tree of a graph .*)
val pseudoentry : t

(** The pseudo-exit label. Primarily useful for computing the
    dominator tree of a graph .*)
val pseudoexit : t

(** Returns [true] if the label is [pseudoentry] or [pseudoexit]. *)
val is_pseudo : t -> bool

include Cgen_utils.Regular.S with type t := t

(** A specialized tree data structure for labels, implemented
    as a PATRICIA tree. *)
module Tree : Patricia_tree_intf.S with type key := t

(** Same as [Tree], but for sets of labels. *)
module Tree_set : Patricia_tree_intf.Set
  with type key := t
   and type 'a map := 'a Tree.t

(** An open-addressing hash table keyed by labels. *)
module Dense_table : Dense_intf.Map with type key := t

(** An open-addressing hash set of labels. *)
module Dense_set : Dense_intf.Set with type key := t

(** A directed graph data structure. *)
module Graph : sig
  type t
  type node = label

  type edge = private {
    src : label;
    dst : label;
  }

  (** The empty graph. *)
  val empty : t

  (** Returns all nodes in the graph. *)
  val nodes : t -> node Sequence.t

  (** Returns all edges in the graph. *)
  val edges : t -> edge Sequence.t

  (** Returns the number of nodes in the graph. *)
  val number_of_nodes : t -> int

  (** Returns the number of edges in the graph. *)
  val number_of_edges : t -> int

  module Node : sig
    (** All successors of a node. *)
    val succs : node -> t -> node Sequence.t

    (** All predecessors of a node. *)
    val preds : node -> t -> node Sequence.t

    (** All outgoing edges of a node.  *)
    val outputs : node -> t -> edge Sequence.t

    (** All incoming edges of a node. *)
    val inputs : node -> t -> edge Sequence.t

    (** Inserts a node into the graph. *)
    val insert : node -> t -> t

    (** Removes a node from the graph (along with its associated edges). *)
    val remove : node -> t -> t

    (** The edge degree of a node. *)
    val degree : ?dir:[`In | `Out] -> node -> t -> int

    (** Test for membership of a node in the graph. *)
    val mem : node -> t -> bool

    (** [has_edge src dst g] returns [true] if the edge from [src] to
        [dst] exists in [g]. *)
    val has_edge : node -> node -> t -> bool
  end

  module Edge : sig
    (** The predecessor node of an edge. *)
    val src : edge -> node

    (** The successor node of an edge. *)
    val dst : edge -> node

    (** [create s d] constructs an edge from source [s] to destination [d]. *)
    val create : node -> node -> edge

    (** Inserts an edge into the graph.

        If the source or destination nodes don't yet exist in the graph, then
        they are inserted.
    *)
    val insert : edge -> t -> t

    (** Removes an edge from the graph. *)
    val remove : edge -> t -> t
  end
end

(** An interface for connecting entry and exit nodes of the graph
    with [pseudoentry] and [pseudoexit], respectively. *)
module Pseudo : sig
  val add : Graph.t -> Graph.t
end
