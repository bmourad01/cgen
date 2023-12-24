module Data_ = Data

open Core

include Common

type insn = Insn.t [@@deriving bin_io, compare, equal, sexp]
type ctrl = Ctrl.t [@@deriving bin_io, compare, equal, sexp]
type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]
type slot = Slot.t [@@deriving bin_io, compare, equal, sexp]
type func = Func.t [@@deriving bin_io, compare, equal, sexp]
type cfg = Cfg.t
type live = Live.t
type loops = Loops.t
type data = Data_.t [@@deriving bin_io, compare, equal, sexp]
type module_ = Module.t

module Insn = Insn
module Eval = Eval
module Ctrl = Ctrl
module Blk = Blk
module Slot = Slot
module Func = Func
module Cfg = Cfg
module Live = Live
module Loops = Loops
module Data = Data_
module Module = Module

module Abi = Abi
