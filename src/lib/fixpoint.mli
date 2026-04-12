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

(** [run (module G) ?rev ?step ?edge ~start ~init ~equal ~merge ~f g]
    computes a dataflow fixpoint over [g], starting from the [start] node.

    [~rev:true] reverses the graph direction, useful for backward analyses
    such as liveness. Defaults to [false].

    [~step] is an optional per-node hook called as
    [step visit_count node old_val new_val]; used for widening.

    [~edge] is an optional per-edge hook called as
    [edge src dst val] before merging into the successor; used for
    path-sensitive narrowing.

    @raise Invalid_argument if [start] is not a node in [g].
*)
val run :
  (module Label.Graph_s with type t = 'g) ->
  ?rev:bool ->
  ?step:(int -> Label.t -> 'd -> 'd -> 'd) ->
  ?edge:(Label.t -> Label.t -> 'd -> 'd) ->
  start:Label.t ->
  init:'d Solution.t ->
  equal:('d -> 'd -> bool) ->
  merge:('d -> 'd -> 'd) ->
  f:(Label.t -> 'd -> 'd) ->
  'g ->
  'd Solution.t
