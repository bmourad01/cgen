module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func
module Cfg = Pseudo_cfg
module Live = Pseudo_live.Make

type 'a insn = 'a Insn.t [@@deriving bin_io, compare, equal, sexp]
type 'a blk = 'a Blk.t [@@deriving bin_io, compare, equal, sexp]
type 'a func = 'a Func.t [@@deriving bin_io, compare, equal, sexp]
