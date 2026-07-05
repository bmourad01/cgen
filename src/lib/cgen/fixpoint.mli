(** Iterative dataflow analysis *)

(** A dataflow solution mapping labels to abstract values. *)
module Solution : sig
  type 'd t

  (** [create constraints default] creates an initial solution seeded
      with [constraints], using [default] for all unspecified nodes. *)
  val create : 'd Label.Tree.t -> 'd -> 'd t

  (** [get t l] returns the value for [l], or the default if absent. *)
  val get : 'd t -> Label.t -> 'd

  (** [default t] returns the default value. *)
  val default : 'd t -> 'd
end

(** [run ?rev ?step ?edge ~start ~init ~equal ~merge ~f g]
    computes a dataflow fixpoint over [g], starting from the [start] node,
    with the initial approximation of the solution [init].

    [equal] defines the equality relation of the abstract domain being
    computed. This relation is important for ensuring termination of the
    analysis (i.e. the analysis terminates when no new changes are added
    to the system of dataflow equations).

    [merge] defines the "join" or "meet" relation over the abstract domain.
    It is used to combine predecessor states with successor states, thus
    propagating information across the graph.

    [f] is the "transfer" function for a node in the graph: given an incoming
    state, a new state is returned.

    If [rev = true], the graph direction is reversed. This is useful for
    backward analyses such as liveness. Defaults to [false].

    [step] is an optional per-node hook called as
    [step visit_count node old_val new_val]; used for widening.

    [edge] is an optional per-edge hook called as
    [edge src dst value] before merging into [dst]; used for
    path-sensitive narrowing.

    Raises [Invalid_argument] if [start] is not a node in [g].
*)
val run :
  ?rev:bool ->
  ?step:(int -> Label.t -> 'd -> 'd -> 'd) ->
  ?edge:(Label.t -> Label.t -> 'd -> 'd) ->
  start:Label.t ->
  init:'d Solution.t ->
  equal:('d -> 'd -> bool) ->
  merge:('d -> 'd -> 'd) ->
  f:(Label.t -> 'd -> 'd) ->
  Label.Graph.t ->
  'd Solution.t
