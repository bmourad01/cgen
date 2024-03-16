type insn = Abi_insn.t [@@deriving bin_io, compare, equal, sexp]
type ctrl = Abi_ctrl.t [@@deriving bin_io, compare, equal, sexp]
type blk = Abi_blk.t [@@deriving bin_io, compare, equal, sexp]
type func = Abi_func.t [@@deriving bin_io, compare, equal, sexp]
type cfg = Abi_cfg.t
type live = Abi_live.t

module Insn = Abi_insn
module Ctrl = Abi_ctrl
module Blk = Abi_blk
module Func = Abi_func
module Cfg = Abi_cfg
module Live = Abi_live
