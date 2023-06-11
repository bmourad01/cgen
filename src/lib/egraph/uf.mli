type t

val create : unit -> t
val fresh : t -> Id.t
val find : t -> Id.t -> Id.t
val union : t -> Id.t -> Id.t -> Id.t
