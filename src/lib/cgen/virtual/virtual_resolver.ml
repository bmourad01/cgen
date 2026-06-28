open Regular.Std
open Cgen_containers

include Virtual_resolver_impl.Make(struct
    type lhs = Var.t option
    let iter_vars_of_lhs = Base.Option.iter
    module Insn = Virtual_insn
    module Ctrl = Virtual_ctrl
    module Blk = Virtual_blk
    module Func = struct
      include Virtual_func
      let iter_args ?(rev = false) fn ~f =
        iter_args ~rev fn ~f:(fun (x, _) -> f x)
    end
  end)
