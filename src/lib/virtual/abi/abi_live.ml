include Virtual_live_impl.Make(struct
    module Insn = struct
      type t = Abi_insn.t
      let lhs = Abi_insn.def
    end
    module Blk = Abi_blk
    module Func = Abi_func
    module Cfg = Abi_cfg
  end)
