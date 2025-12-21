open Regular.Std

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

open Graphlib.Std

(** [check (module G) ?dom g entry] determines if graph [g] is reducible
    when starting from the [entry] node. *)
val check :
  (module Graph
    with type t = 't
     and type edge = 'e
     and type node = 'n) ->
  ?dom:'n Semi_nca.tree ->
  't ->
  'n ->
  bool
