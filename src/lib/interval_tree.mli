open Interval_tree_intf

module Make(I : Interval) : S
  with type key := I.t
   and type point := I.point
