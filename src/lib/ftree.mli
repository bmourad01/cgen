(** A finger tree data structure; for internal use only. *)

open Regular.Std

type 'a t [@@deriving bin_io, compare, equal, sexp]

val last_exn : 'a t -> 'a
val head_exn : 'a t -> 'a
val last : 'a t -> 'a option
val head : 'a t -> 'a option
val singleton : 'a -> 'a t
val empty : 'a t
val is_empty : 'a t -> bool
val fold_left : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b
val fold_right : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b
val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b
val iter : 'a t -> f:('a -> unit) -> unit
val iter_rev : 'a t -> f:('a -> unit) -> unit
val map : 'a t -> f:('a -> 'b) -> 'b t
val map_rev : 'a t -> f:('a -> 'b) -> 'b t
val of_list : 'a list -> 'a t
val of_list_rev : 'a list -> 'a t
val cons : 'a t -> 'a -> 'a t
val snoc : 'a t -> 'a -> 'a t
val rear : 'a t -> ('a t * 'a) option
val front : 'a t -> ('a t * 'a) option
val tail : 'a t -> 'a t option
val init : 'a t -> 'a t option
val rear_exn : 'a t -> 'a t * 'a
val front_exn : 'a t -> 'a t * 'a
val tail_exn : 'a t -> 'a t
val init_exn : 'a t -> 'a t
val reverse : 'a t -> 'a t
val split : 'a t -> f:(int -> bool) -> 'a t * 'a t
val length : 'a t -> int
val append : 'a t -> 'a t -> 'a t
val split_at_exn : 'a t -> int -> 'a t * 'a t
val split_at : 'a t -> int -> ('a t * 'a t) option
val lookup_exn : 'a t -> f:(int -> bool) -> 'a 
val lookup : 'a t -> f:(int -> bool) -> 'a option
val get_exn : 'a t -> int -> 'a
val get : 'a t -> int -> 'a option
val set : 'a t -> int -> 'a -> 'a t
val update : 'a t -> int -> f:('a -> 'a) -> 'a t
val compare : 'a t -> 'a t -> compare:('a -> 'a -> int) -> int
val equal : 'a t -> 'a t -> equal:('a -> 'a -> bool) -> bool
val insert : 'a t -> 'a -> int -> 'a t
val filter : 'a t -> f:('a -> bool) -> 'a t
val enum : ?rev:bool -> 'a t -> 'a seq
val find : 'a t -> f:('a -> bool) -> 'a option
val findi : 'a t -> f:(int -> 'a -> bool) -> (int * 'a) option
val exists : 'a t -> f:('a -> bool) -> bool
val next : 'a t -> f:('a -> bool) -> 'a option
val prev : 'a t -> f:('a -> bool) -> 'a option
val remove : 'a t -> int -> 'a t
val remove_if : 'a t -> f:('a -> bool) -> 'a t
val update_if : 'a t -> 'a -> f:('a -> bool) -> 'a t
val to_list : 'a t -> 'a list

val pp :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> unit) ->
  Format.formatter ->
  'a t ->
  unit
