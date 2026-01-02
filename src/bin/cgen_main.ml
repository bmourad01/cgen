open Core
open Regular.Std
open Cgen

let dump_ok (opts : Cli.t) = match opts.ifmt with
  | IFstructured -> true
  | IFvirtual -> match opts.dump with
    | Dparse | Dssa | Drestructure_preopt | Dmiddle | Drestructure
    | Dabi | Disel | Disel_dce | Dregalloc | Dpeephole | Dasm -> true
    | Ddestructure -> false

let comp_virtual' (opts : Cli.t) ppf close bail m =
  let open Context.Syntax in
  let* tenv, m = Passes.initialize m in
  if Cli.equal_dump opts.dump Dssa then begin
    if not opts.nc then Format.fprintf ppf ";; After SSA transformation:\n\n%!";
    Format.fprintf ppf "%a\n%!" Virtual.Module.pp m;
    bail ();
  end;
  let* () = Context.when_ (Cli.equal_dump opts.dump Drestructure_preopt) @@ fun () ->
    let+ m = Passes.restructure ~tenv m in
    if not opts.nc then Format.fprintf ppf ";; After restructuring (pre-optimizations):\n\n%!";
    Format.fprintf ppf "%a\n%!" Structured.Module.pp m;
    bail () in
  let* tenv, m = Passes.optimize tenv m in
  if Cli.equal_dump opts.dump Dmiddle then begin
    if not opts.nc then Format.fprintf ppf ";; After middle-end-optimizations:\n\n%!";
    Format.fprintf ppf "%a\n%!" Virtual.Module.pp m;
    bail ();
  end;
  let* () = Context.when_ (Cli.equal_dump opts.dump Drestructure) @@ fun () ->
    let+ m = Passes.restructure ~tenv m in
    if not opts.nc then Format.fprintf ppf ";; After restructuring (post-optimizations):\n\n%!";
    Format.fprintf ppf "%a\n%!" Structured.Module.pp m;
    bail () in
  let* m = Passes.to_abi tenv m in
  let* m = Passes.optimize_abi m in
  if Cli.equal_dump opts.dump Dabi then begin
    if not opts.nc then Format.fprintf ppf ";; After ABI lowering\n\n%!";
    Format.fprintf ppf "%a\n%!" Virtual.Abi.Module.pp m;
    bail ();
  end;
  let* (module Machine) = Context.machine in
  let* m = Passes.isel (module Machine) m in
  if Cli.equal_dump opts.dump Disel then begin
    if not opts.nc then Format.fprintf ppf ";; After instruction selection:\n\n%!";
    Format.fprintf ppf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  let module Remove_deads = Pseudo_passes.Remove_dead_insns(Machine) in
  let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
  if Cli.equal_dump opts.dump Disel_dce then begin
    if not opts.nc then Format.fprintf ppf ";; After dead-code elimination (isel):\n\n%!";
    Format.fprintf ppf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  let* m = Passes.regalloc (module Machine) m in
  if Cli.equal_dump opts.dump Dregalloc then begin
    if not opts.nc then Format.fprintf ppf ";; After register allocation:\n\n%!";
    Format.fprintf ppf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  let m = Pseudo.Module.map_funs m ~f:Machine.Peephole.run in
  let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
  if Cli.equal_dump opts.dump Dpeephole then begin
    if not opts.nc then Format.fprintf ppf ";; After peephole optimizations:\n\n%!";
    Format.fprintf ppf "%a\n%!" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m;
    bail ();
  end;
  assert (Cli.equal_dump opts.dump Dasm);
  let module Emit = Pseudo_passes.Emit(Machine) in
  Format.fprintf ppf "%a%!" Emit.emit m;
  !!(close ())

let comp_virtual (opts : Cli.t) =
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
    if not opts.nc then Format.fprintf ppf ";; After parsing\n\n%!";
    Format.fprintf ppf "%a\n%!" Virtual.Module.pp m;
    bail ();
  end;
  comp_virtual' opts ppf close bail m

let comp_structured (opts : Cli.t) =
  let open Context.Syntax in
  let* m = match opts.file with
    | Ifile file -> Parse.Structured.from_file file
    | Istdin -> Parse.Structured.from_stdin () in
  let ppf, close = match opts.output with
    | Ostdout -> Format.std_formatter, Fn.id
    | Ofile file ->
      let oc = Out_channel.create file in
      Format.formatter_of_out_channel oc,
      (fun () -> Out_channel.close oc) in
  let bail () = close (); Cli.bail () in
  if Cli.equal_dump opts.dump Dparse then begin
    if not opts.nc then Format.fprintf ppf ";; After parsing\n\n%!";
    Format.fprintf ppf "%a\n%!" Structured.Module.pp m;
    bail ();
  end;
  let* m = Passes.destructure m in
  if Cli.equal_dump opts.dump Ddestructure then begin
    if not opts.nc then Format.fprintf ppf ";; After destructuring\n\n%!";
    Format.fprintf ppf "%a\n%!" Virtual.Module.pp m;
    bail ();
  end;
  comp_virtual' opts ppf close bail m

let comp (opts : Cli.t) =
  if dump_ok opts then match opts.ifmt with
    | IFvirtual -> comp_virtual opts
    | IFstructured -> comp_structured opts
  else
    Context.failf "input/dump combination %S and %S is invalid"
      (Cli.string_of_input_fmt opts.ifmt) (Cli.string_of_dump opts.dump) ()

let () =
  Cli.run @@ fun opts ->
  Context.init opts.target |>
  Context.run (comp opts) |>
  Or_error.iter_error ~f:(fun err ->
      Cli.fatal "%a\n%!" Error.pp err ())
