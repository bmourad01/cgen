open Core
open Regular.Std
open Cgen

let comp filename =
  let open Context.Syntax in
  let* m = Parse.Virtual.from_file filename in
  let* tenv, m = Passes.initialize m in
  Format.printf "After SSA transformation:\n\n%!";
  Format.printf "%a\n%!" Virtual.Module.pp m;
  let* tenv, m = Passes.optimize tenv m in
  Format.printf "=================================================\n%!";
  Format.printf "After middle-end optimizations:\n\n%!";
  Format.printf "%a\n%!" Virtual.Module.pp m;
  Format.printf "=================================================\n%!";
  let* m = Passes.to_abi tenv m in
  let* m = Passes.optimize_abi m in
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
