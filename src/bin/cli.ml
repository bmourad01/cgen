open Cmdliner

(* Why is this here, when we have `Cgen.Target.find`?

   The targets should be getting declared at the toplevel in their
   respective modules, but the evaluation of these modules is not
   guaranteed to happen by the time we start parsing command-line
   arguments.

   It just so happens that, for the front-end executable, we should
   know all of the out-of-the-box targets provided by the library,
   so this feels like a tolerable compromise in the design of extending
   the supported targets.
*)
let targets =
  Core.Map.of_alist_exn (module Core.String) @@
  Core.List.map ~f:(fun t -> Cgen.Target.name t, t) @@
  Cgen.Machine.[
    X86.Amd64_sysv.target;
  ]

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
    Core.Map.data targets |>
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

let go f file output dump nc target =
  let file = match file with
    | "" -> Istdin
    | _ -> Ifile file in
  let output = match output with
    | None -> Ostdout
    | Some out -> Ofile out in
  let dump = match dump_of_string_opt dump with
    | None -> fatal "invalid dump option: %s\n%!" dump ()
    | Some d -> d in
  let target = match Core.Map.find targets target with
    | None -> fatal "invalid target: %s\n%!" target ()
    | Some t -> t in
  f {file; output; dump; nc; target}

let t f = Term.(const (go f) $ file $ output $ dump $ dump_no_comment $ target)

let man = List.concat [
    man_dump;
    man_targets;
  ]

let info =
  let doc = "The cgen compiler backend" in
  Cmd.info "cgen" ~doc ~man ~version:"0.1" ~exits:Cmd.Exit.defaults

let run f = exit @@ Cmd.eval @@ Cmd.v info (t f)
