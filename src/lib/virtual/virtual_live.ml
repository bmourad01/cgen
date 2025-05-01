open Core

include Virtual_live_impl.Make(struct
    module Insn = struct
      type t = Virtual_insn.t
      let lhs = Fn.compose Virtual_common.var_set_of_option Virtual_insn.lhs
    end
    module Blk = Virtual_blk
    module Func = Virtual_func
    module Cfg = Virtual_cfg
  end)
