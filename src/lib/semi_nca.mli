(** Implements the SEMI-NCA algorithm.

    This is a known efficient algorithm for computing the
    dominator tree of a graph.
*)

open Regular.Std
open Graphlib.Std

(** The dominator tree *)
type 'a tree

module Tree : sig
  type 'a t = 'a tree

  (** The root of the tree.

      Invariant: [parent t (root t) = None].
  *)
  val root : 'a t -> 'a

  (** Immediate parent of a node. *)
  val parent : 'a t -> 'a -> 'a option

  (** Immediate children of a node. *)
  val children : 'a t -> 'a -> 'a seq

  (** All descendants of a node in preorder. *)
  val descendants : 'a t -> 'a -> 'a seq

  (** All ancestors of a node, in ascending order. *)
  val ancestors : 'a t -> 'a -> 'a seq

  (** [is_descendant_of t ~parent n] returns [true] if [n]
      is a descendant of [parent] in [t]. *)
  val is_descendant_of : 'a t -> parent:'a -> 'a -> bool

  (** Returns a postorder traversal of the tree, starting from
      the root. *)
  val postorder : 'a t -> 'a seq

  (** Equivalent to [descendants t (root t)]. *)
  val preorder : 'a t -> 'a seq
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
