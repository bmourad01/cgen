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

(** [run (module G) ?start ?rev ?step ~init ~equal ~merge ~f g] computes
    a dataflow fixpoint over [g], starting from [start] (default:
    [Label.pseudoentry]).

    [~rev:true] reverses the graph direction, useful for backward analyses
    such as liveness.

    [~step] is an optional per-node hook called as
    [step visit_count node old_val new_val]; used for widening.
*)
val run :
  (module Label.Graph_s with type t = 'g) ->
  ?start:Label.t ->
  ?rev:bool ->
  ?step:(int -> Label.t -> 'd -> 'd -> 'd) ->
  init:'d Solution.t ->
  equal:('d -> 'd -> bool) ->
  merge:('d -> 'd -> 'd) ->
  f:(Label.t -> 'd -> 'd) ->
  'g ->
  'd Solution.t
