module Blk = Pseudo_blk
module Func = Pseudo_func

type 'a blk = 'a Blk.t [@@deriving sexp]
type 'a func = 'a Func.t [@@deriving sexp]

module Make_select = Pseudo_select.Make
