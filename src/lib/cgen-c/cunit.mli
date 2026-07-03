(** A translation unit: the top-level result of parsing a single
    C source file.

    Parameterized over an annotation type ['a] in the
    "Trees That Grow" style: a parser supplies [Location.t],
    while hand-written ASTs can supply [unit].
*)

(** A translation unit, holding its top-level declarations in
    source order. *)
type 'a t [@@deriving bin_io, compare, equal, hash, sexp]

(** Builds a translation unit from a list of declarations. *)
val create : 'a Decl.t list -> 'a t

(** The top-level declarations of the unit, in source order. *)
val decls : 'a t -> 'a Decl.t list

(** {1 Pretty printer} *)

(** Renders the unit in C syntax: each declaration in order,
    separated by a blank line. *)
val pp : Format.formatter -> 'a t -> unit

(** [to_string u] is [pp] rendered to a string. *)
val to_string : 'a t -> string
