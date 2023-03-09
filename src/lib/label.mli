(** A generic program label.

    The scope of each label is limited to the body of a function.

    Globally-scoped locations, or {b symbols} in our parlance, should
    be referred to by name.
*)

open Regular.Std

(** A program label. *)
type t

(** The pseudo-entry label. Primarily useful for computing the
    dominator tree of a graph .*)
val pseudoentry : t

(** The pseudo-exit label. Primarily useful for computing the
    dominator tree of a graph .*)
val pseudoexit : t

(** Returns [true] if the label is [pseudoentry] or [pseudoexit]. *)
val is_pseudo : t -> bool

include Regular.S with type t := t
