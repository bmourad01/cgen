module Stmt = Structured_stmt
module Func = Structured_func

type stmt = Stmt.t [@@deriving bin_io, compare, equal, sexp]
type slot = Virtual.Slot.t [@@deriving bin_io, compare, equal, sexp]
