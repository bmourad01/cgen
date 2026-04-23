open Dense_intf

module Make_map(K : Key) : Map with type key = K.t
module Make_set(K : Key) : Set with type key = K.t
