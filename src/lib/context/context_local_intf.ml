module type S = sig
  type 'a context

  (** [set k v] sets the value associated with key [k] to [v]. *)
  val set : 'a Dict.tag -> 'a -> unit context

  (** [get k] returns the value [Some v] associated with [k] if it
      exists, and [None] otherwise. *)
  val get : 'a Dict.tag -> 'a option context

  (** [get' k ~default] returns the value associated with [k] if it exists,
      and [default] otherwise. *)
  val get' : 'a Dict.tag -> default:'a -> 'a context

  (** [get_err k] returns the value associated with [k] if it exists,
      and terminates the computation with an error otherwise. *)
  val get_err : 'a Dict.tag -> 'a context

  (** [erase k] removes [k] from the local state. This can be useful to
      reset the state for re-runs or to discard state that is isolated to
      a particular analysis or transformation. *)
  val erase : 'a Dict.tag -> unit context
end
