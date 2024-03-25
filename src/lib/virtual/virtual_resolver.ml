open Regular.Std

include Virtual_resolver_impl.Make(struct
    type lhs = Var.t option
    let vars_of_lhs = Option.to_list
    module Insn = Virtual_insn
    module Ctrl = Virtual_ctrl
    module Blk = Virtual_blk
    module Func = struct
      include Virtual_func
      let args ?rev t = args ?rev t |> Seq.map ~f:fst
    end
  end)
