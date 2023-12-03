include Abi_common

type insn = Abi_insn.t [@@deriving bin_io, compare, equal, sexp]
type ctrl = Abi_ctrl.t [@@deriving bin_io, compare, equal, sexp]
type blk = Abi_blk.t [@@deriving bin_io, compare, equal, sexp]
type func = Abi_func.t [@@deriving bin_io, compare, equal, sexp]

module Insn = Abi_insn
module Ctrl = Abi_ctrl
module Blk = Abi_blk
module Func = Abi_func
