open Core
open Regular.Std
open Cgen_containers

include Virtual_resolver_impl.Make(struct
    type lhs = Var.Tree_set.t
    let iter_vars_of_lhs = Var.Tree_set.iter
    module Insn = struct
      include Abi_insn
      let lhs = def
    end
    module Ctrl = Abi_ctrl
    module Blk = Abi_blk
    module Func = struct
      include Abi_func
      let iter_args ?(rev = false) fn ~f =
        iter_args ~rev fn ~f:(function
            | `stk (x, _), _
            | `reg (x, _), _ -> f x)
    end
  end)
