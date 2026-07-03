open Core
open Cgen_utils

module Cpp = struct
  type t = {
    prog : string;
    args : string list;
  }

  let create ~prog ?(args = []) () = {prog; args}

  let add_args t extra = {t with args = t.args @ extra}

  (* A bare preprocessor with `-undef`, so it strips the host compiler's
     predefined macros.

     We supply our own target-derived identity (see `Predef`) instead of
     inheriting the host's.

     Standard macros (e.g. `__STDC__`, `__STDC_VERSION__`) survive `-undef`.
  *)
  let default = {prog = "cpp"; args = ["-undef"]}

  let normalize cmd =
    String.split_on_chars cmd ~on:[' '; '\t'] |>
    List.filter ~f:(Fn.non String.is_empty)

  let of_command cmd = match normalize cmd with
    | prog :: args -> {prog; args}
    | [] -> default
end

let pp_exception ppf = function
  | Failure msg -> Format.pp_print_string ppf msg
  | C_lexer.Lex_error msg -> Format.pp_print_string ppf msg
  | _ -> Format.pp_print_string ppf "invalid syntax"

(* Reset the per-parse mutable state and seed the lexbuf's file name
   (line markers may override it). *)
let prepare (lexbuf : Lexing.lexbuf) ~file =
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = file};
  Lexer_hack.reset ();
  (* `__builtin_va_list` is a predefined typedef name (the compiler
     builtin that `<stdarg.h>` typically aliases as `va_list`); seed
     it so the lexer classifies it as a type name. *)
  Lexer_hack.define_typedef "__builtin_va_list";
  Parse_state.cur_typedef := false;
  Parse_state.anon_counter := 0;
  Parse_state.source_map := Source_map.create ()

let run lexbuf ~file =
  prepare lexbuf ~file;
  match C_parser.translation_unit C_lexer.token lexbuf with
  | u -> Ok u
  | exception exn ->
    let loc =
      Source_map.location_of !Parse_state.source_map
        lexbuf.Lexing.lex_start_p lexbuf.Lexing.lex_curr_p in
    Error (Diagnostic.error ~location:loc (Format.asprintf "%a" pp_exception exn))

let run_cpp (cpp : Cpp.t) ~input ?stdin () : (string, Diagnostic.t) result =
  match Process.run ?stdin cpp.prog (cpp.args @ [input]) with
  | exception exn ->
    let d =
      Diagnostic.error @@ Format.sprintf
        "could not run preprocessor '%s': %s"
        cpp.prog (Exn.to_string exn) in
    Error d
  | {code = Exited 0; stdout; _} -> Ok stdout
  | {code; stderr; _} ->
    let detail = match code with
      | Exited n -> Format.sprintf "exited with status %d" n
      | Signaled n -> Format.sprintf "was killed by signal %d" n in
    let err = String.strip stderr in
    let d =
      Diagnostic.error @@
      Format.sprintf "preprocessor '%s' %s%s"
        cpp.prog detail
        (if String.is_empty err then "" else ":\n" ^ err) in
    Error d

let lex_result ~file : (string, Diagnostic.t) result -> _ = function
  | Error _ as e -> e
  | Ok text -> run (Lexing.from_string text) ~file

let from_string s = run (Lexing.from_string s) ~file:"<input>"

let from_file ?cpp name = match cpp with
  | Some cpp -> run_cpp cpp ~input:name () |> lex_result ~file:name
  | None ->
    let f c = run (Lexing.from_channel c) ~file:name in
    match In_channel.with_file name ~f with
    | exception Sys_error msg -> Error (Diagnostic.error msg)
    | r -> r

let from_channel ?cpp ?(file = "<stdin>") ic = match cpp with
  | None -> run (Lexing.from_channel ic) ~file
  | Some cpp ->
    let stdin = In_channel.input_all ic in
    run_cpp cpp ~input:"-" ~stdin () |> lex_result ~file

let from_stdin ?cpp () = from_channel ?cpp ~file:"<stdin>" In_channel.stdin
