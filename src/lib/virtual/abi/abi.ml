include Abi_common

type insn = Abi_insn.t [@@deriving bin_io, compare, equal, sexp]
type ctrl = Abi_ctrl.t [@@deriving bin_io, compare, equal, sexp]

module Insn = Abi_insn
module Ctrl = Abi_ctrl
