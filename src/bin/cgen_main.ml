open Core
open Regular.Std
open Cgen

let isel m ~f =
  let open Context.Syntax in
  let+ funs =
    Virtual.Abi.Module.funs m |>
    Context.Seq.map ~f >>|
    Seq.to_list in
  Pseudo.Module.create ()
    ~dict:(Virtual.Abi.Module.dict m)
    ~data:(Virtual.Abi.Module.data m |> Seq.to_list)
    ~name:(Virtual.Abi.Module.name m) ~funs

let pseudo_map_funs m ~f =
  let open Context.Syntax in
  let+ funs =
    Pseudo.Module.funs m |>
    Context.Seq.map ~f >>|
    Seq.to_list in
  Pseudo.Module.with_funs m funs

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
  let* m = isel m ~f:Isel.run in
  Format.printf "=================================================\n%!";
  Format.printf "After instruction selection:\n\n%!";
  Format.printf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
  let module Remove_deads = Pseudo.Remove_dead_insns(Machine) in
  let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
  Format.printf "=================================================\n%!";
  Format.printf "After removing dead instructions:\n\n%!";
  Format.printf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
  let module RA = Regalloc.IRC(Machine)(Context) in
  let* m = pseudo_map_funs m ~f:RA.run in
  Format.printf "=================================================\n%!";
  Format.printf "After register allocation:\n\n%!";
  Format.printf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
  let module Layout = Regalloc.Layout_stack(Machine)(Context) in
  let* m = pseudo_map_funs m ~f:Layout.run in
  Format.printf "=================================================\n%!";
  Format.printf "After stack layout:\n\n%!";
  Format.printf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
  !!()

let () =
  let args = Sys.get_argv () in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.run (comp args.(1)) |>
  Or_error.iter_error ~f:(Format.eprintf "%a\n%!" Error.pp)
