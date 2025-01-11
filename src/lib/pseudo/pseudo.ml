module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func
module Cfg = Pseudo_cfg
module Live = Pseudo_live.Make
module Remove_dead_insns = Pseudo_remove_dead_insns.Make

type 'a insn = 'a Insn.t [@@deriving bin_io, compare, equal, sexp]
type 'a blk = 'a Blk.t [@@deriving bin_io, compare, equal, sexp]
type ('a , 'b) func = ('a, 'b) Func.t [@@deriving bin_io, compare, equal, sexp]
