module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func
module Module = Pseudo_module
module Cfg = Pseudo_cfg

type 'a insn = 'a Insn.t [@@deriving bin_io, compare, equal, sexp]
type 'a blk = 'a Blk.t [@@deriving bin_io, compare, equal, sexp]
type ('a, 'b) func = ('a, 'b) Func.t [@@deriving bin_io, compare, equal, sexp]
type ('a, 'b) module_ = ('a, 'b) Module.t [@@deriving bin_io, compare, equal, sexp]
