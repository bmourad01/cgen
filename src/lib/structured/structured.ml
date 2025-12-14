module Stmt = Structured_stmt
module Func = Structured_func
module Module = Structured_module
module Destructure = Structured_destructure.Make

type stmt = Stmt.t [@@deriving bin_io, compare, equal, sexp]
type slot = Virtual.Slot.t [@@deriving bin_io, compare, equal, sexp]
type func = Func.t [@@deriving bin_io, compare, equal, sexp]
type module_ = Module.t [@@deriving bin_io, compare, equal, sexp]
