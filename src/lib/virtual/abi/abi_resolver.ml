include Virtual_resolver_impl.Make(struct
    type lhs = Var.Set.t
    module Insn = struct
      include Abi_insn
      let lhs = def
    end
    module Blk = Abi_blk
    module Func = Abi_func
  end)
