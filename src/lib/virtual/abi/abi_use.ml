include Virtual_use_impl.Make(struct
    module Insn = Abi_insn
    module Ctrl = Abi_ctrl
    module Blk = Abi_blk
    module Func = Abi_func
  end)
