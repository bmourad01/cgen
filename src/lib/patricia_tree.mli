open Patricia_tree_intf

module Make(K : Key) : S with type key := K.t
