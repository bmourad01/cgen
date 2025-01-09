module Blk = Pseudo_blk
module Func = Pseudo_func
module Cfg = Pseudo_cfg

type 'a blk = 'a Blk.t [@@deriving bin_io, compare, equal, sexp]
type 'a func = 'a Func.t [@@deriving bin_io, compare, equal, sexp]
