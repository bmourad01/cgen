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

let comp (opts : Cli.t) =
  let open Context.Syntax in
  let* m = match opts.file with
    | `file file -> Parse.Virtual.from_file file
    | `stdin -> Parse.Virtual.from_stdin () in
  if Cli.equal_dump opts.dump Dparse then begin
    Format.printf ";; After parsing:@;@.%a\n%!"
      Virtual.Module.pp m;
    Cli.bail ();
  end;
  let* tenv, m = Passes.initialize m in
  if Cli.equal_dump opts.dump Dssa then begin
    Format.printf ";; After SSA transformation:@;@.%a\n%!"
      Virtual.Module.pp m;
    Cli.bail ();
  end;
  let* tenv, m = Passes.optimize tenv m in
  if Cli.equal_dump opts.dump Dmiddle then begin
    Format.printf ";; After middle-end-optimizations:@;@.%a\n%!"
      Virtual.Module.pp m;
    Cli.bail ();
  end;
  let* m = Passes.to_abi tenv m in
  let* m = Passes.optimize_abi m in
  if Cli.equal_dump opts.dump Dabi then begin
    Format.printf ";; After ABI lowering:@;@.%a\n%!"
      Virtual.Abi.Module.pp m;
    Cli.bail ();
  end;
  let* (module Machine) = Context.machine in
  let module Isel = Isel.Make(Machine)(Context) in
  let* m = isel m ~f:Isel.run in
  if Cli.equal_dump opts.dump Disel then begin
    Format.printf ";; After instruction selection:@;@.%a\n%!"
      (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    Cli.bail ();
  end;
  let module Remove_deads = Pseudo.Remove_dead_insns(Machine) in
  let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
  if Cli.equal_dump opts.dump Disel_dce then begin
    Format.printf ";; After dead-code elimination (isel):@;@.%a\n%!"
      (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    Cli.bail ();
  end;
  let module RA = Regalloc.IRC(Machine)(Context) in
  let* m = pseudo_map_funs m ~f:RA.run in
  if Cli.equal_dump opts.dump Dregalloc then begin
    Format.printf ";; After register allocation:@;@.%a\n%!"
      (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    Cli.bail ();
  end;
  assert (Cli.equal_dump opts.dump Dasm);
  let module Emit = Pseudo.Emit(Machine) in
  Format.printf "%a%!" Emit.emit m;
  !!()

let () =
  Cli.run @@ fun opts ->
  Context.init opts.target |>
  Context.run (comp opts) |>
  Or_error.iter_error ~f:(fun err ->
      Cli.fatal "%a\n%!" Error.pp err ())
