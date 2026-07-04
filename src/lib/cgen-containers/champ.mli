(** CHAMP (Compressed Hash Array-Mapped Prefix Tree) *)

module Make(K : Champ_intf.Key) : Champ_intf.S with type key = K.t
