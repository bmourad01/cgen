(** An immutable, ordered map optimized for very small sizes. *)

module Make(Key : Small_map_intf.Key) : Small_map_intf.S with type key = Key.t
