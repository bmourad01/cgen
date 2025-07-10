open Core
open Regular.Std
open Cgen

let comp (opts : Cli.t) =
  let open Context.Syntax in
  let* m = match opts.file with
    | Ifile file -> Parse.Virtual.from_file file
    | Istdin -> Parse.Virtual.from_stdin () in
  let ppf, close = match opts.output with
    | Ostdout -> Format.std_formatter, Fn.id
    | Ofile file ->
      let oc = Out_channel.create file in
      Format.formatter_of_out_channel oc,
      (fun () -> Out_channel.close oc) in
  let bail () = close (); Cli.bail () in
  if Cli.equal_dump opts.dump Dparse then begin
    Format.fprintf ppf ";; After parsing:@;@.%a\n%!"
      Virtual.Module.pp m;
    bail ();
  end;
  let* tenv, m = Passes.initialize m in
  if Cli.equal_dump opts.dump Dssa then begin
    Format.fprintf ppf ";; After SSA transformation:@;@.%a\n%!"
      Virtual.Module.pp m;
    bail ();
  end;
  let* tenv, m = Passes.optimize tenv m in
  if Cli.equal_dump opts.dump Dmiddle then begin
    Format.fprintf ppf ";; After middle-end-optimizations:@;@.%a\n%!"
      Virtual.Module.pp m;
    bail ();
  end;
  let* m = Passes.to_abi tenv m in
  let* m = Passes.optimize_abi m in
  if Cli.equal_dump opts.dump Dabi then begin
    Format.fprintf ppf ";; After ABI lowering:@;@.%a\n%!"
      Virtual.Abi.Module.pp m;
    bail ();
  end;
  let* (module Machine) = Context.machine in
  let* m = Passes.isel (module Machine) m in
  if Cli.equal_dump opts.dump Disel then begin
    Format.fprintf ppf ";; After instruction selection:@;@.%a\n%!"
      (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  let module Remove_deads = Pseudo_passes.Remove_dead_insns(Machine) in
  let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
  if Cli.equal_dump opts.dump Disel_dce then begin
    Format.fprintf ppf ";; After dead-code elimination (isel):@;@.%a\n%!"
      (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  let* m = Passes.regalloc (module Machine) m in
  if Cli.equal_dump opts.dump Dregalloc then begin
    Format.fprintf ppf ";; After register allocation:@;@.%a\n%!"
      (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  let m = Pseudo.Module.map_funs m ~f:Machine.Peephole.run in
  if Cli.equal_dump opts.dump Dpeephole then begin
    Format.fprintf ppf ";; After peephole optimizations:@;@.%a\n%!"
      (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  assert (Cli.equal_dump opts.dump Dasm);
  let module Emit = Pseudo_passes.Emit(Machine) in
  Format.fprintf ppf "%a%!" Emit.emit m;
  !!(close ())

let () =
  Cli.run @@ fun opts ->
  Context.init opts.target |>
  Context.run (comp opts) |>
  Or_error.iter_error ~f:(fun err ->
      Cli.fatal "%a\n%!" Error.pp err ())
