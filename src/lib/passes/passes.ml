open Regular.Std
open Virtual
open Context.Syntax

module Abi_loadopt = Abi_loadopt
module Egraph_opt = Egraph_opt
module Lower_abi = Lower_abi
module Promote_slots = Promote_slots
module Remove_dead_vars = Remove_dead_vars
module Remove_disjoint_blks = Remove_disjoint_blks
module Resolve_constant_blk_args = Resolve_constant_blk_args
module Sccp = Sccp
module Simplify_cfg = Simplify_cfg
module Ssa = Ssa

let initialize m =
  let* target = Context.target in
  let m = Module.map_funs m ~f:Remove_disjoint_blks.run in
  let*? tenv = Typecheck.run m ~target in
  let*? m = Module.map_funs_err m ~f:Ssa.run in
  !!(tenv, m)

let retype tenv m =
  Module.funs m |>
  Seq.to_list |> Typecheck.update_fns tenv

let optimize tenv m =
  let module Cv = Context.Virtual in
  let*? m = Module.map_funs_err m ~f:Promote_slots.run in
  let*? tenv = retype tenv m in
  let*? m = Module.map_funs_err m ~f:(Sccp.run tenv) in
  let m = Module.map_funs m ~f:Remove_disjoint_blks.run in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let* m = Context.Virtual.Module.map_funs m ~f:(Simplify_cfg.run tenv) in
  let*? tenv = retype tenv m in
  let* m = Cv.Module.map_funs m ~f:(Egraph_opt.run tenv) in
  let*? tenv = retype tenv m in
  let m = Module.map_funs m ~f:Remove_disjoint_blks.run in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let*? m = Module.map_funs_err m ~f:Resolve_constant_blk_args.run in
  let* m = Cv.Module.map_funs m ~f:(Simplify_cfg.run tenv) in
  let*? tenv = retype tenv m in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let*? tenv = retype tenv m in
  !!(tenv, m)

let to_abi tenv m =
  let+ funs =
    Module.funs m |> Seq.to_list |>
    Context.List.map ~f:(Lower_abi.run tenv) in
  Abi.Module.create () ~funs
    ~name:(Module.name m)
    ~dict:(Module.dict m)
    ~data:(Seq.to_list @@ Module.data m)

let optimize_abi m =
  let*? m = Abi.Module.map_funs_err m ~f:Promote_slots.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Abi_loadopt.run in
  let m = Abi.Module.map_funs m ~f:Remove_disjoint_blks.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Remove_dead_vars.run_abi in
  let* () = Context.iter_seq_err (Abi.Module.funs m) ~f:Ssa.check_abi in
  !!m
