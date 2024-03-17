include Virtual_use_impl.Make(struct
    module Insn = Virtual_insn
    module Ctrl = Virtual_ctrl
    module Blk = Virtual_blk
    module Func = Virtual_func
  end)
