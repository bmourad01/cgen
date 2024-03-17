include Virtual_resolver_impl.Make(struct
    type lhs = Var.t option
    module Insn = Virtual_insn
    module Blk = Virtual_blk
    module Func = Virtual_func
  end)
