module Sys_unix = Unix

open Core
open Regular.Std
open Cgen

(* A C source lowers through Structured IR into the full virtual pipeline,
   so every stage is reachable. *)
let dump_ok_c (_ : Cli.t) = true

let dump_ok_structured (opts : Cli.t) = match opts.dump with
  | Delab | Dstructured
    -> false
  | Dparse
  | Dssa
  | Drestructure_preopt
  | Dmiddle
  | Ddestructure
  | Drestructure
  | Dabi
  | Disel
  | Disel_dce
  | Dregalloc
  | Dpeephole
  | Dasm
    -> true

let dump_ok_virtual (opts : Cli.t) = match opts.dump with
  | Dparse
  | Dssa
  | Drestructure_preopt
  | Dmiddle
  | Drestructure
  | Dabi
  | Disel
  | Disel_dce
  | Dregalloc
  | Dpeephole
  | Dasm
    -> true
  | Ddestructure | Delab | Dstructured
    -> false

let dump_ok (opts : Cli.t) = match opts.ifmt with
  | IFc -> dump_ok_c opts
  | IFstructured -> dump_ok_structured opts
  | IFvirtual -> dump_ok_virtual opts

let comp_virtual' (opts : Cli.t) ppf close bail m =
  let open Context.Syntax in
  let* tenv, m = Passes.initialize ~invariants:opts.invariants m in
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
  let* tenv, m = Passes.optimize ~invariants:opts.invariants tenv m in
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
  let* m = Passes.to_abi ~invariants:opts.invariants tenv m in
  let* m = Passes.optimize_abi ~invariants:opts.invariants m in
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
  let* m = Passes.regalloc ~invariants:opts.invariants (module Machine) m in
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
    if not opts.nc then Format.fprintf ppf "// After parsing\n\n%!";
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

let isatty c = try Sys_unix.isatty c with _ -> false

let use_color () =
  Option.is_none (Sys.getenv "NO_COLOR") && isatty Sys_unix.stderr

let report_diagnostic (d : Cgen_utils.Diagnostic.t) =
  let sm = Cgen_utils.Source_map.create () in
  Cli.fatal "%a\n%!" (Cgen_utils.Diagnostic.pp_with_source ~color:(use_color ()) sm) d ()

(* Print accumulated non-fatal diagnostics to stderr; compilation continues. *)
let report_warnings = function
  | [] -> ()
  | ws ->
    let color = use_color () in
    let sm = Cgen_utils.Source_map.create () in
    List.iter ws ~f:(fun w ->
        Format.eprintf "%a\n%!" (Cgen_utils.Diagnostic.pp_with_source ~color sm) w)

let comp_c (opts : Cli.t) =
  let open Context.Syntax in
  (* By default C inputs are preprocessed with `cpp -undef` (overridable via
     `--cpp`, disabled with `--no-cpp`). cgen supplies its own target-derived
     predefines rather than inheriting the host compiler's identity. *)
  let cpp =
    if opts.no_cpp then None
    else
      let base = Cgen_c.Parse.Cpp.of_command opts.cpp in
      Some (Cgen_c.Parse.Cpp.add_args base (Cgen_c.Predef.defines opts.target)) in
  let parsed = match opts.file with
    | Ifile file -> Cgen_c.Parse.from_file ?cpp file
    | Istdin -> Cgen_c.Parse.from_stdin ?cpp () in
  match parsed with
  | Error d -> report_diagnostic d
  | Ok u ->
    let ppf, close = match opts.output with
      | Ostdout -> Format.std_formatter, Fn.id
      | Ofile file ->
        let oc = Out_channel.create file in
        Format.formatter_of_out_channel oc,
        (fun () -> Out_channel.close oc) in
    let bail () = close (); Cli.bail () in
    if Cli.equal_dump opts.dump Dparse then begin
      if not opts.nc then Format.fprintf ppf "// After parsing\n\n%!";
      Format.fprintf ppf "%a\n%!" Cgen_c.Cunit.pp u;
      bail ()
    end;
    (* The data model comes from the selected target. *)
    let dmodel = Target.data_model opts.target in
    match Cgen_c.Elab.elab u ~dmodel ~loc_of_ann:Option.some with
    | Error d -> report_diagnostic d
    | Ok (t, warnings) ->
      if not opts.no_warnings then report_warnings warnings;
      if Cli.equal_dump opts.dump Delab then begin
        if not opts.nc then Format.fprintf ppf "// After elaboration\n\n%!";
        Format.fprintf ppf "%a\n%!" Cgen_c.Tcunit.pp t;
        bail ()
      end;
      let name = match opts.file with
        | Istdin -> "a"
        | Ifile file ->
          try Filename.chop_extension (Filename.basename file)
          with _ -> Filename.basename file in
      let* m = Cgen_c.Lower.module_ ~name t in
      if Cli.equal_dump opts.dump Dstructured then begin
        if not opts.nc then Format.fprintf ppf "// After lowering to Structured IR\n\n%!";
        Format.fprintf ppf "%a\n%!" Structured.Module.pp m;
        bail ()
      end;
      let* m = Passes.destructure m in
      if Cli.equal_dump opts.dump Ddestructure then begin
        if not opts.nc then Format.fprintf ppf ";; After destructuring\n\n%!";
        Format.fprintf ppf "%a\n%!" Virtual.Module.pp m;
        bail ()
      end;
      comp_virtual' opts ppf close bail m

let comp (opts : Cli.t) =
  if dump_ok opts then match opts.ifmt with
    | IFvirtual -> comp_virtual opts
    | IFstructured -> comp_structured opts
    | IFc -> comp_c opts
  else
    Context.failf "input (%S) and dump (%S) combination is invalid"
      (Cli.string_of_input_fmt opts.ifmt) (Cli.string_of_dump opts.dump) ()

(* Since this program is short-lived, just prioritize GC throughput. *)
let setup_gc () =
  let opts = Stdlib.Gc.get () in
  Stdlib.Gc.set {opts with space_overhead = 2000}

let has_env var = match Sys.getenv var with
  | Some _ -> true
  | None -> false

let setup_gc_unless_overridden () =
  if not (has_env "OCAMLRUNPARAM" || has_env "CAMLRUNPARAM")
  then setup_gc ()

let error_message err =
  let rec atoms = function
    | Sexp.Atom a -> [a]
    | Sexp.List xs -> List.concat_map xs ~f:atoms in
  match atoms (Error.sexp_of_t err) with
  | [] -> Error.to_string_hum err
  | parts -> String.concat parts ~sep:": "

let () =
  setup_gc_unless_overridden ();
  Cli.run @@ fun opts ->
  Context.init opts.target |>
  Context.run (comp opts) |>
  Or_error.iter_error ~f:(fun err ->
      Cli.fatal "%s\n%!" (error_message err) ())
