(** A mutable, dynamically-sized array; for internal use only. *)

open Core
open Regular.Std

type 'a t

val create : ?capacity:int -> unit -> 'a t
val length : 'a t -> int
val is_empty : 'a t -> bool
val capacity : 'a t -> int
val copy : 'a t -> 'a t
val clear : 'a t -> unit
val append : 'a t -> 'a t -> unit
val unsafe_get : 'a t -> int -> 'a
val unsafe_set : 'a t -> int -> 'a -> unit
val push : 'a t -> 'a -> unit
val pop_exn : 'a t -> 'a
val pop : 'a t -> 'a option
val get_exn : 'a t -> int -> 'a
val get : 'a t -> int -> 'a option
val front_exn : 'a t -> 'a
val front : 'a t -> 'a option
val back_exn : 'a t -> 'a
val back : 'a t -> 'a option
val set_exn : 'a t -> int -> 'a -> unit
val set : 'a t -> int -> 'a -> unit Or_error.t

val fold_until :
  'a t ->
  init:'b ->
  f:('b -> 'a -> ('b, 'c) Continue_or_stop.t) ->
  finish:('b -> 'c) ->
  'c

val foldi : 'a t -> init:'b -> f:(int -> 'b -> 'a -> 'b) -> 'b
val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b
val fold_right : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b
val iteri : 'a t -> f:(int -> 'a -> unit) -> unit
val iter : 'a t -> f:('a -> unit) -> unit
val findi : 'a t -> f:(int -> 'a -> bool) -> 'a option
val find : 'a t -> f:('a -> bool) -> 'a option
val find_mapi : 'a t -> f:(int -> 'a -> 'b option) -> 'b option
val find_map : 'a t -> f:('a -> 'b option) -> 'b option
val mapi_inplace : 'a t -> f:(int -> 'a -> 'a) -> unit
val map_inplace : 'a t -> f:('a -> 'a) -> unit
val mapi : 'a t -> f:(int -> 'a -> 'b) -> 'b t
val map : 'a t -> f:('a -> 'b) -> 'b t
val filteri : 'a t -> f:(int -> 'a -> bool) -> 'a t
val filter : 'a t -> f:('a -> bool) -> 'a t
val filter_mapi : 'a t -> f:(int -> 'a -> 'b option) -> 'b t
val filter_map : 'a t -> f:('a -> 'b option) -> 'b t
val filteri_inplace : 'a t -> f:(int -> 'a -> bool) -> unit
val filter_inplace : 'a t -> f:('a -> bool) -> unit
val to_array : 'a t -> 'a array
val to_list : 'a t -> 'a list
val to_list_rev : 'a t -> 'a list
val to_sequence_mutable : 'a t -> 'a seq
val to_sequence_rev_mutable : 'a t -> 'a seq
val to_sequence : 'a t -> 'a seq
val to_sequence_rev : 'a t -> 'a seq
val of_array : 'a array -> 'a t
val of_list : 'a list -> 'a t
val sort : ?pos:int -> ?len:int -> 'a t -> compare:('a -> 'a -> int) -> unit
