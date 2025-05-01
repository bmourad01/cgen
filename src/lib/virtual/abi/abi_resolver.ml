open Core
open Regular.Std

include Virtual_resolver_impl.Make(struct
    type lhs = Var.Set.t
    let vars_of_lhs = Set.to_list
    module Insn = struct
      include Abi_insn
      let lhs = def
    end
    module Ctrl = Abi_ctrl
    module Blk = Abi_blk
    module Func = struct
      include Abi_func
      let args ?rev t =
        args ?rev t |> Seq.map ~f:(fun (a, _) -> match a with
            | `stk (x, _) | `reg (x, _) -> x)
    end
  end)
