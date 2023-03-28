module Data_ = Data

open Core
open Graphlib.Std
open Monads.Std
open Regular.Std

include Common

type edge = Edge.t [@@deriving bin_io, compare, equal, sexp]
type blk = Blk.t [@@deriving bin_io, compare, equal, sexp]
type func = Func.t [@@deriving bin_io, compare, equal, sexp]
type cfg = Cfg.t
type live = Live.t
type data = Data_.t [@@deriving bin_io, compare, equal, sexp]
type module_ = Module.t

module Insn = Insn
module Edge = Edge
module Blk = Blk
module Func = Func
module Cfg = Cfg
module Live = Live
module Data = Data_
module Module = Module
