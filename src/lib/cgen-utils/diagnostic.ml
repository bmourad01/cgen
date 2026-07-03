open Core

type severity =
  | Error
  | Warning
  | Note
[@@deriving compare, equal, hash, sexp]

type t = {
  severity : severity;
  location : Location.t option;
  message  : string;
} [@@deriving compare, equal, hash, sexp]

let make ?location ~severity message = {severity; location; message}

let error   ?location message = make ?location ~severity:Error   message
let warning ?location message = make ?location ~severity:Warning message
let note    ?location message = make ?location ~severity:Note    message

let format_to ?location severity fmt =
  let buf = Buffer.create 128 in
  let ppf = Format.formatter_of_buffer buf in
  let kon ppf () =
    Format.pp_print_flush ppf ();
    make ?location ~severity (Buffer.contents buf) in
  Format.kfprintf kon ppf fmt

let errorf   ?location fmt = format_to ?location Error   fmt
let warningf ?location fmt = format_to ?location Warning fmt
let notef    ?location fmt = format_to ?location Note    fmt

let severity_string = function
  | Error   -> "error"
  | Warning -> "warning"
  | Note    -> "note"

let ansi_reset = "\027[0m"
let ansi_bold  = "\027[1m"
let ansi_caret = "\027[1;32m" (* bold green *)

let ansi_severity = function
  | Error   -> "\027[1;31m"   (* bold red *)
  | Warning -> "\027[1;35m"   (* bold magenta *)
  | Note    -> "\027[1;36m"   (* bold cyan *)

let pp_header ?(color = false) ppf t =
  let esc s = if color then s else "" in
  Option.iter t.location ~f:(fun loc ->
      Format.fprintf ppf "%s%a:%s "
        (esc ansi_bold)
        Location.pp loc
        (esc ansi_reset));
  Format.fprintf ppf "%s%s%s: %s"
    (esc (ansi_severity t.severity))
    (severity_string t.severity)
    (esc ansi_reset)
    t.message

let pp ppf t = pp_header ppf t

let to_string t = Format.asprintf "%a" pp t

let pp_underline ?(color = false) ppf ~line ~start_col ~end_col =
  let n = String.length line in
  for i = 0 to start_col - 2 do
    Format.pp_print_char ppf
      (if i < n && Char.equal line.[i] '\t' then '\t' else ' ')
  done;
  if color then Format.pp_print_string ppf ansi_caret;
  Format.pp_print_char ppf '^';
  for _ = start_col + 1 to end_col - 1 do
    Format.pp_print_char ppf '~'
  done;
  if color then Format.pp_print_string ppf ansi_reset

let pp_excerpt ?(color = false) sm ppf loc =
  let line = Location.line (Location.start loc) in
  match Source_map.line_text sm ~file:(Location.file loc) line with
  | None -> ()
  | Some text ->
    let start_col = Location.column (Location.start loc) in
    (* Clamp a multi-line range to the end of the first line. *)
    let end_col =
      if Location.line (Location.end_ loc) = line
      then Location.column (Location.end_ loc)
      else String.length text + 1 in
    let w = String.length (Int.to_string line) in
    Format.fprintf ppf "@\n %*d | %s@\n %*s | " w line text w "";
    pp_underline ~color ppf ~line:text ~start_col ~end_col

let pp_with_source ?(color = false) sm ppf t =
  pp_header ~color ppf t;
  Option.iter t.location ~f:(pp_excerpt ~color sm ppf)

let to_string_with_source ?color sm t =
  Format.asprintf "%a" (pp_with_source ?color sm) t

let to_error t = Error.of_string (to_string t)
let of_error e = error (Error.to_string_hum e)

let severity t = t.severity
let location t = t.location
let message  t = t.message
