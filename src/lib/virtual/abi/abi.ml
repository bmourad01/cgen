include Abi_common

type insn = Abi_insn.t [@@deriving bin_io, compare, equal, sexp]

module Insn = Abi_insn
