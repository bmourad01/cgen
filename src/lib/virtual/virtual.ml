open Core

include Virtual_common

module Insn = Virtual_insn
module Eval = Virtual_eval
module Ctrl = Virtual_ctrl
module Blk = Virtual_blk
module Slot = Virtual_slot
module Func = Virtual_func
module Cfg = Virtual_cfg
module Live = Virtual_live
module Use = Virtual_use
module Resolver = Virtual_resolver
module Loops = Virtual_loops
module Data = Virtual_data
module Module = Virtual_module

type insn = Insn.t [@@deriving bin_io, compare, equal, sexp]
type ctrl = Ctrl.t [@@deriving bin_io, compare, equal, sexp]
type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]
type slot = Slot.t [@@deriving bin_io, compare, equal, sexp]
type func = Func.t [@@deriving bin_io, compare, equal, sexp]
type cfg = Cfg.t
type live = Live.t
type use = Use.t
type resolver = Resolver.t
type loops = Loops.t
type data = Data.t [@@deriving bin_io, compare, equal, sexp]
type module_ = Module.t

module Abi = Abi
