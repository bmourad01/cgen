open Bitset_intf

module Make(K : Key) : S with type key := K.t
module Id : S with type key := int
