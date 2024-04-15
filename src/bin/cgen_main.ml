open Core
open Regular.Std
open Cgen

let pp_sep ppf () = Format.fprintf ppf "@.@."

let err f = Fn.compose Context.lift_err f

let retype tenv m =
  Virtual.Module.funs m |>
  Seq.to_list |> Typecheck.update_fns tenv

let comp filename =
  let open Context.Syntax in
  let* target = Context.target in
  let* m = Parse.Virtual.from_file filename in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? tenv = Typecheck.run m ~target in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Ssa.run in
  Format.printf "%a\n%!" Virtual.Module.pp m;
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Promote_slots.run in
  let*? tenv = retype tenv m in
  let*? m = Virtual.Module.map_funs_err m ~f:(Passes.Sccp.run tenv) in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  let* m = Context.Virtual.Module.map_funs m ~f:Passes.Simplify_cfg.run in
  let*? tenv = retype tenv m in
  let m = Virtual.Module.map_funs m ~f:Passes.Resolve_constant_blk_args.run in
  let* m = Context.Virtual.Module.map_funs m ~f:(Passes.Egraph_opt.run tenv) in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  let* m = Context.Virtual.Module.map_funs m ~f:Passes.Simplify_cfg.run in
  let*? tenv = retype tenv m in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  Format.printf "=================================================\n%!";
  Format.printf "%a\n%!" Virtual.Module.pp m;
  Format.printf "=================================================\n%!";
  let*? tenv =
    Virtual.Module.funs m |>
    Seq.to_list |> Typecheck.update_fns tenv in
  let* fns =
    Virtual.Module.funs m |> Seq.to_list |>
    Context.List.map ~f:(Passes.Lower_abi.run tenv) in
  let* fns = Context.List.map fns ~f:(err Passes.Promote_slots.run_abi) in
  let* fns = Context.List.map fns ~f:(err Passes.Abi_loadopt.run) in
  let fns = List.map fns ~f:Passes.Remove_disjoint_blks.run_abi in
  let* fns = Context.List.map fns ~f:(err Passes.Remove_dead_vars.run_abi) in
  Format.printf "@[<v 0>%a@]\n%!"
    (Format.pp_print_list ~pp_sep Virtual.Abi.Func.pp) fns;
  !!()

let () =
  let args = Sys.get_argv () in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.run (comp args.(1)) |>
  Or_error.iter_error ~f:(Format.eprintf "%a\n%!" Error.pp)
