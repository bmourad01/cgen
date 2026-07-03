open Core

type pos = {
  byte   : int;
  line   : int;
  column : int;
} [@@deriving bin_io, compare, equal, hash, sexp]

type t = {
  file  : string;
  start : pos;
  end_  : pos;
} [@@deriving bin_io, compare, equal, hash, sexp]

let byte   p = p.byte
let line   p = p.line
let column p = p.column

let file  t = t.file
let start t = t.start
let end_  t = t.end_

let create_pos_exn ~byte ~line ~column =
  if byte < 0 then
    invalid_arg "Location.create_pos: byte must be non-negative";
  if line < 0 then
    invalid_arg "Location.create_pos: line must be non-negative";
  if column < 0 then
    invalid_arg "Location.create_pos: column must be non-negative";
  {byte; line; column}

let create_pos ~byte ~line ~column =
  try Ok (create_pos_exn ~byte ~line ~column)
  with Invalid_argument msg -> Or_error.error_string msg

let create_exn ~file ~start ~end_ =
  if start.byte > end_.byte then
    invalid_arg "Location.create: start must not come after end_";
  {file; start; end_}

let create ~file ~start ~end_ =
  try Ok (create_exn ~file ~start ~end_)
  with Invalid_argument msg -> Or_error.error_string msg

let merge a b =
  let start = if a.start.byte <= b.start.byte then a.start else b.start in
  let end_  = if a.end_.byte  >= b.end_.byte  then a.end_  else b.end_  in
  {file = a.file; start; end_}

let pp ppf t =
  if t.start.line = t.end_.line then
    Format.fprintf ppf "%s:%d:%d-%d"
      t.file t.start.line t.start.column t.end_.column
  else
    Format.fprintf ppf "%s:%d:%d-%d:%d"
      t.file t.start.line t.start.column t.end_.line t.end_.column

let to_string t = Format.asprintf "%a" pp t
