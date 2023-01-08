(** A program variable. *)

open Regular.Std

(** An identifier for temporary variables. This is for internal
    use only and should not be directly constructed by a user. *)
type id

(** A program variable. *)
type t

(** Returns [true] if the variable is a temporary. *)
val is_temp : t -> bool

(** Returns [true] if the variable has a specific name. *)
val is_named : t -> bool

(** Returns the name of the variable, if it exists. *)
val name : t -> string option

(** The index of the variable. This corresponds to a specific
    version of the variable and is used primarily for maintaining
    SSA form. *)
val index : t -> int

(** Returns the variable with a given index. *)
val with_index : t -> int -> t

(** [base x] is equivalent to [with_index x 0], where [0] is the
    index of the original version of [x]. *)
val base : t -> t

(** [same x y] returns [true] if [x] and [y] refer to the same
    variable. Note that [index x] and [index y] are allowed to
    differ. *)
val same : t -> t -> bool

(** [create name ?index] creates a named variable, with an optional
    [index] (by default, it is [0]). *)
val create : ?index:int -> string -> t

(** Creates a temporary variable.

    This is not meant to be called by a user, and is for internal use
    only. For generating fresh temporaries, use [Context.Var.fresh].
*)
val temp : ?index:int -> id -> t

include Regular.S with type t := t
