(** Implements the SEMI-NCA algorithm.

    This is a known efficient, linear-time algorithm for computing
    the dominator tree of a graph.
*)

open Regular.Std
open Graphlib.Std

(** The dominator tree *)
type 'a tree

module Tree : sig
  type 'a t = 'a tree

  exception Not_found

  (** Returns [true] if this tree was computed via a graph
      with edges reversed.

      This affects downstream methods such as [rpo], as these
      will reflect a DFS traversal that started from the exit
      node and walked backwards via incoming edges.
  *)
  val is_reversed : 'a t -> bool

  (** The root of the tree.

      Invariant: [parent t (root t) = None].
  *)
  val root : 'a t -> 'a

  (** Immediate parent of a node. *)
  val parent : 'a t -> 'a -> 'a option

  (** Returns [true] if the node is a member of the tree. *)
  val mem : 'a t -> 'a -> bool

  (** Immediate parent of a node.

      @raise Not_found if no parent exists
  *)
  val parent_exn : 'a t -> 'a -> 'a

  (** Depth of a node in the tree. *)
  val depth : 'a t -> 'a -> int option

  (** Depth of a node in the tree.

      @raise Not_found if the node is not a member of the tree.
  *)
  val depth_exn : 'a t -> 'a -> int

  (** Returns the reverse postorder numbering of the node,
      if it exists in the tree. *)
  val rpo : 'a t -> 'a -> int option

  (** Returns the reverse postorder numbering of the node.

      @raise Not_found if the node is not a member of the tree.
  *)
  val rpo_exn : 'a t -> 'a -> int

  (** Immediate children of a node, in reverse postorder. *)
  val children : 'a t -> 'a -> 'a seq

  (** All descendants of a node in preorder. *)
  val descendants : 'a t -> 'a -> 'a seq

  (** All ancestors of a node, in ascending order. *)
  val ancestors : 'a t -> 'a -> 'a seq

  (** [is_descendant_of t ~parent n] returns [true] if [n]
      is a descendant of [parent] in [t].

      This encodes the relation of whether [parent] strictly
      dominates [n].
  *)
  val is_descendant_of : 'a t -> parent:'a -> 'a -> bool

  (** Same as [is_descendant_of], but adds reflexivity to the relation. *)
  val dominates : 'a t -> 'a -> 'a -> bool

  (** Returns a postorder traversal of the tree, starting from
      the root. *)
  val postorder : 'a t -> 'a seq

  (** Equivalent to [descendants t (root t)]. *)
  val preorder : 'a t -> 'a seq

  (** Returns the lowest common ancestor (LCA) of two nodes
      in the tree. *)
  val lca : 'a t -> 'a -> 'a -> 'a option

  (** Returns the lowest common ancestor (LCA) of two nodes
      in the tree.

      @raise Not_found if the LCA does not exist
  *)
  val lca_exn : 'a t -> 'a -> 'a -> 'a
end

(** The dominance frontier *)
type 'a frontier

module Frontier : sig
  type 'a t = 'a frontier

  (** [enum f n] returns the frontier for a node [n] in [f]. *)
  val enum : 'a t -> 'a -> 'a seq

  (** [mem f a b] returns [true] if the frontier for [a] in [f] contains [b]. *)
  val mem : 'a t -> 'a -> 'a -> bool
end

(** [compute (module G) ?rev g entry] computes the dominator tree
    for [g], starting at the node [entry].

    If [rev] is true, then the resulting tree corresponds to the
    post-dominance relation.
*)
val compute :
  (module Graph
    with type t = 't
     and type edge = 'e
     and type node = 'n) ->
  ?rev:bool ->
  't ->
  'n ->
  'n tree

(** Computes the dominance frontier from an existing dominator
    tree. *)
val frontier :
  (module Graph
    with type t = 't
     and type edge = 'e
     and type node = 'n) ->
  't ->
  'n tree ->
  'n frontier
