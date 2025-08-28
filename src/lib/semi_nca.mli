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
  val parent : 'a t -> 'a -> 'a option
  val children : 'a t -> 'a -> 'a seq
  val descendants : 'a t -> 'a -> 'a seq
  val ancestors : 'a t -> 'a -> 'a seq
  val is_descendant_of : 'a t -> parent:'a -> 'a -> bool
end

(** The dominance frontier *)
type 'a frontier

module Frontier : sig
  type 'a t = 'a frontier
  val enum : 'a t -> 'a -> 'a seq
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
  ?rev:bool ->
  't ->
  'n tree ->
  'n frontier
