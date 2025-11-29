open Cmdliner

let () = Cgen.Machine.force_initialization ()

let bail () = exit Cmd.Exit.ok

let fatal fmt =
  let kon ppf () =
    Format.pp_print_flush ppf ();
    exit Cmd.Exit.internal_error in
  Format.kfprintf kon Format.err_formatter fmt

let file =
  let doc =
    "The input .vir program. If no file is provided, then the \
     program is read from stdin." in
  Arg.(value &
       pos 0 file "" &
       info [] ~docv:"FILE" ~doc)

type dump =
  | Dparse
  | Dssa
  | Dmiddle
  | Dabi
  | Disel
  | Disel_dce
  | Dregalloc
  | Dpeephole
  | Dasm
[@@deriving equal]

let string_of_dump = function
  | Dparse -> "parse"
  | Dssa -> "ssa"
  | Dmiddle -> "middle"
  | Dabi -> "abi"
  | Disel -> "isel"
  | Disel_dce -> "isel-dce"
  | Dregalloc -> "regalloc"
  | Dpeephole -> "peephole"
  | Dasm -> "asm"

let dump_of_string_opt = function
  | "parse" -> Some Dparse
  | "ssa" -> Some Dssa
  | "middle" -> Some Dmiddle
  | "abi" -> Some Dabi
  | "isel" -> Some Disel
  | "isel-dce" -> Some Disel_dce
  | "regalloc" -> Some Dregalloc
  | "peephole" -> Some Dpeephole
  | "asm" -> Some Dasm
  | _ -> None

let man_dump =
  `S "DUMP" ::
  `Pre "Options for dumping stages of the compiler" :: begin
    Core.List.map ~f:(fun (d, desc) ->
        `I (string_of_dump d ^ ":", desc)) [
      Dparse, "dump the IR after parsing";
      Dssa, "dump the IR after SSA transformation";
      Dmiddle, "dump the IR after middle-end optimizations";
      Dabi, "dump the IR after ABI lowering";
      Disel, "dump the IR after instruction selection";
      Disel_dce, "dump the IR after dead code elimination (after instruction selection)";
      Dregalloc, "dump the IR after register allocation";
      Dpeephole, "dump the IR after target-specific peephole optimizations";
      Dasm, "dump the finalized assembly program";
    ]
  end

let dump = 
  let doc = "Option to dump a stage of the compiler" in
  Arg.(value &
       opt string (string_of_dump Dasm)
         (info ["d"; "dump"] ~docv:"DUMP" ~doc))

let dump_no_comment =
  let doc = "Don't include a descriptive comment when dumping" in
  Arg.(value & flag (info ["dump-no-comment"] ~doc))

let man_targets =
  `S "TARGET" ::
  `Pre "Supported target platforms" :: begin
    Cgen.Target.enum_targets () |>
    Core.Sequence.to_list |>
    Core.List.map ~f:(fun t ->
        `P (Format.asprintf "%a" Cgen.Target.pp t))
  end

let target =
  let doc = "The target platform" in
  Arg.(value &
       opt string "amd64-sysv"
         (info ["t"; "target"] ~docv:"TARGET" ~doc))

let output =
  let doc = "The output file. If no file is provided, then the output \
             is printed to stdout." in
  Arg.(value &
       opt (some string) None
         (info ["o"; "output"] ~docv:"OUTPUT" ~doc))

type input =
  | Ifile of string
  | Istdin

type output =
  | Ofile of string
  | Ostdout

type t = {
  file   : input;
  output : output;
  dump   : dump;
  nc     : bool;
  target : Cgen.Target.t;
}

let log_env = Cmd.Env.info "CGEN_LOG"

let setup_log level =
  Logs.set_level level;
  Logs.set_reporter @@ Logs_fmt.reporter ()

let go f file output dump nc target log_level =
  setup_log log_level;
  let file = match file with
    | "" -> Istdin
    | _ -> Ifile file in
  let output = match output with
    | None -> Ostdout
    | Some out -> Ofile out in
  let dump = match dump_of_string_opt dump with
    | None -> fatal "invalid dump option: %s\n%!" dump ()
    | Some d -> d in
  let target = match Cgen.Target.find target with
    | None -> fatal "invalid target: %s\n%!" target ()
    | Some t -> t in
  f {file; output; dump; nc; target}

let t f =
  let open Term in
  const (go f) $
  file $
  output $
  dump $
  dump_no_comment $
  target $
  Logs_cli.level ~env:log_env ()

let man = List.concat [
    man_dump;
    man_targets;
  ]

let info =
  let doc = "The cgen compiler backend" in
  Cmd.info "cgen" ~doc ~man ~version:"0.1" ~exits:Cmd.Exit.defaults

let run f = exit @@ Cmd.eval @@ Cmd.v info (t f)
