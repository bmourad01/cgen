open Core

module type S = sig
  type t

  val from_string : string -> t Context.t
  val from_file : string -> t Context.t
end

let file_pos ?filename lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  let f = match filename with
    | None -> "<none>"
    | Some f -> f in
  Format.sprintf "%s:%d:%d" f l c

let try_parse ?filename lexbuf ~f = try f () with
  | _ ->
    Context.fail @@
    Error.createf "Parser error: %s" @@
    file_pos lexbuf ?filename

let with_file name ~f = try In_channel.with_file name ~f with
  | Sys_error msg -> Context.fail @@ Error.createf "%s" msg

module Virtual = struct
  type t = Virtual.module_

  let from_string s =
    let lexbuf = Lexing.from_string s in
    try_parse lexbuf ~f:(fun () ->
        Virtual_parser.module_ Virtual_lexer.token lexbuf)

  let from_file name = with_file name ~f:(fun chan ->
      let lexbuf = Lexing.from_channel chan in
      try_parse lexbuf ~f:(fun () ->
          Virtual_parser.module_ Virtual_lexer.token lexbuf)
        ~filename:name)
end
