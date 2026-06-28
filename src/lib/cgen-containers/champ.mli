(** CHAMP (Compressed Hash Array-Mapped Prefix Tree) *)

module Make(K : Base.Hashtbl.Key.S) : Champ_intf.S with type key = K.t
