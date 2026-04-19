(** Reducibility of a CFG (control flow graph).

    A CFG [G] is reducible iff every cycle in [G] has a unique
    entry node.

    An example of a reducible CFG:

    {v
    entry
      |
      v
    [ H ] <────┐
      |        │
      v        │
    [ B ] ─────┘
      |
      v
     exit
   v}

    Here, [H] is a {i header} of a natural loop with {i body} [B],
    and thus [H] is the unique entry of the cycle [{H,B}].

    An example of an irreducible CFG:

    {v
           entry
           /   \
          v     v
    ┌─> [ A ] [ B ]
    |      \   /
    │       v v
    │      [ C ]
    │        |
    └────────┘
   v}

    For the cycle [{A,C}], there is no unique entry ([A] and [B] are
    equally valid candidates).
*)

(** [check (module G) ?dom g entry] determines if graph [g] is reducible
    when starting from the [entry] node. *)
val check :
  (module Label.Graph_s with type t = 'g) ->
  ?dom:Semi_nca.tree ->
  'g ->
  Label.t ->
  bool
