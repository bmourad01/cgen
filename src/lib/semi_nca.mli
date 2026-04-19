(** Implements the SEMI-NCA algorithm.

    This is a known efficient, linear-time algorithm for computing
    the dominator tree of a graph.
*)

open Regular.Std
open Graphlib.Std

(** The dominator tree *)
type tree

module Tree : sig
  type t = tree

  exception Not_found

  (** Returns [true] if this tree was computed via a graph
      with edges reversed.

      This affects downstream methods such as [rpo], as these
      will reflect a DFS traversal that started from the exit
      node and walked backwards via incoming edges.
  *)
  val is_reversed : t -> bool

  (** The root of the tree.

      Invariant: [parent t (root t) = None].
  *)
  val root : t -> Label.t

  (** Immediate parent of a node. *)
  val parent : t -> Label.t -> Label.t option

  (** Returns [true] if the node is a member of the tree. *)
  val mem : t -> Label.t -> bool

  (** Immediate parent of a node.

      @raise Not_found if no parent exists
  *)
  val parent_exn : t -> Label.t -> Label.t

  (** Depth of a node in the tree. *)
  val depth : t -> Label.t -> int option

  (** Depth of a node in the tree.

      @raise Not_found if the node is not a member of the tree.
  *)
  val depth_exn : t -> Label.t -> int

  (** Returns the reverse postorder numbering of the node,
      if it exists in the tree. *)
  val rpo : t -> Label.t -> int option

  (** Returns the reverse postorder numbering of the node.

      @raise Not_found if the node is not a member of the tree.
  *)
  val rpo_exn : t -> Label.t -> int

  (** Immediate children of a node, in reverse postorder. *)
  val children : t -> Label.t -> Label.t seq

  (** All descendants of a node in preorder. *)
  val descendants : t -> Label.t -> Label.t seq

  (** All ancestors of a node, in ascending order. *)
  val ancestors : t -> Label.t -> Label.t seq

  (** [is_descendant_of t ~parent n] returns [true] if [n]
      is a descendant of [parent] in [t].

      This encodes the relation of whether [parent] strictly
      dominates [n].
  *)
  val is_descendant_of : t -> parent:Label.t -> Label.t -> bool

  (** Same as [is_descendant_of], but adds reflexivity to the relation. *)
  val dominates : t -> Label.t -> Label.t -> bool

  (** Returns a postorder traversal of the tree, starting from
      the root. *)
  val postorder : t -> Label.t seq

  (** Equivalent to [descendants t (root t)]. *)
  val preorder : t -> Label.t seq

  (** Returns the lowest common ancestor (LCA) of two nodes
      in the tree. *)
  val lca : t -> Label.t -> Label.t -> Label.t option

  (** Returns the lowest common ancestor (LCA) of two nodes
      in the tree.

      @raise Not_found if the LCA does not exist
  *)
  val lca_exn : t -> Label.t -> Label.t -> Label.t
end

(** The dominance frontier *)
type frontier

module Frontier : sig
  type t = frontier

  (** [get f n] returns the frontier for a node [n] in [f]. *)
  val get : t -> Label.t -> Label.Tree_set.t

  (** [mem f a b] returns [true] if the frontier for [a] in [f] contains [b]. *)
  val mem : t -> Label.t -> Label.t -> bool
end

(** [compute (module G) ?rev g entry] computes the dominator tree
    for [g], starting at the node [entry].

    If [rev] is true, then the resulting tree corresponds to the
    post-dominance relation.
*)
val compute :
  (module Label.Graph_s with type t = 'g) ->
  ?rev:bool ->
  'g ->
  Label.t ->
  tree

(** Computes the dominance frontier from an existing dominator
    tree. *)
val frontier :
  (module Label.Graph_s with type t = 'g) ->
  'g ->
  tree ->
  frontier
