open Core
open Parse_intf

let file_pos ?filename lexbuf =
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  let f = match filename with
    | None -> "<none>"
    | Some f -> f in
  f, l, c

let pp_exception ppf = function
  | Failure msg -> Format.fprintf ppf "%s" msg
  | _ -> Format.fprintf ppf "invalid syntax"

let try_parse ?filename lexbuf ~f = try f () with
  | exn ->
    let f, l, c = file_pos ?filename lexbuf in
    Context.failf "Parser error: %s:%d:%d, %a" f l c pp_exception exn ()

let with_file name ~f = try In_channel.with_file name ~f with
  | Sys_error msg -> Context.failf "%s" msg ()

module Virtual : S with type t := Virtual.module_ = struct
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
