open Core
open Regular.Std
open Cgen

let retype tenv m =
  Virtual.Module.funs m |>
  Seq.to_list |> Typecheck.update_fns tenv

let to_abi m tenv =
  let open Context.Syntax in
  let+ funs =
    Virtual.Module.funs m |> Seq.to_list |>
    Context.List.map ~f:(Passes.Lower_abi.run tenv) in
  Virtual.Abi.Module.create () ~funs
    ~name:(Virtual.Module.name m)
    ~dict:(Virtual.Module.dict m)
    ~data:(Seq.to_list @@ Virtual.Module.data m)

let comp filename =
  let open Context.Syntax in
  let* target = Context.target in
  let* m = Parse.Virtual.from_file filename in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? tenv = Typecheck.run m ~target in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Ssa.run in
  Format.printf "After SSA transformation:\n\n%!";
  Format.printf "%a\n%!" Virtual.Module.pp m;
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Promote_slots.run in
  let*? tenv = retype tenv m in
  let*? m = Virtual.Module.map_funs_err m ~f:(Passes.Sccp.run tenv) in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  let* m = Context.Virtual.Module.map_funs m ~f:(Passes.Simplify_cfg.run tenv) in
  let*? tenv = retype tenv m in
  let* m = Context.Virtual.Module.map_funs m ~f:(Passes.Egraph_opt.run tenv) in
  let*? tenv = retype tenv m in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Resolve_constant_blk_args.run in
  let* m = Context.Virtual.Module.map_funs m ~f:(Passes.Simplify_cfg.run tenv) in
  let*? tenv = retype tenv m in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  Format.printf "=================================================\n%!";
  Format.printf "After middle-end optimizations:\n\n%!";
  Format.printf "%a\n%!" Virtual.Module.pp m;
  Format.printf "=================================================\n%!";
  let*? tenv = retype tenv m in
  let* m = to_abi m tenv in
  let*? m = Virtual.Abi.Module.map_funs_err m ~f:Passes.Promote_slots.run_abi in
  let*? m = Virtual.Abi.Module.map_funs_err m ~f:Passes.Abi_loadopt.run in
  let m = Virtual.Abi.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run_abi in
  let*? m = Virtual.Abi.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run_abi in
  let* () = Context.iter_seq_err (Virtual.Abi.Module.funs m) ~f:Passes.Ssa.check_abi in
  Format.printf "After ABI lowering:\n\n%!";
  Format.printf "%a\n%!" Virtual.Abi.Module.pp m;
  let* (module Machine) = Context.machine in
  let module Isel = Isel.Make(Machine)(Context) in
  let* pfns =
    Virtual.Abi.Module.funs m |>
    Context.Seq.map ~f:Isel.run >>|
    Seq.to_list in
  Format.printf "=================================================\n%!";
  Format.printf "After instruction selection:\n\n%!";
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n\n")
    (Pseudo.Func.pp Machine.Insn.pp Machine.Reg.pp)
    Format.std_formatter pfns;
  if not @@ List.is_empty pfns then begin
    Format.printf "\n%!";
    Format.printf "=================================================\n%!"
  end;
  let module Remove_deads = Pseudo.Remove_dead_insns(Machine) in
  let pfns = List.map pfns ~f:Remove_deads.run in
  Format.printf "After removing dead instructions:\n\n%!";
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n\n")
    (Pseudo.Func.pp Machine.Insn.pp Machine.Reg.pp)
    Format.std_formatter pfns;
  if not @@ List.is_empty pfns then Format.printf "\n%!";
  !!()

let () =
  let args = Sys.get_argv () in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.run (comp args.(1)) |>
  Or_error.iter_error ~f:(Format.eprintf "%a\n%!" Error.pp)
