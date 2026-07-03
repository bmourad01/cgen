open Core

type info = {
  text  : string;
  lines : int array;
}

(* NB: `None` caches a file we failed to read *)
type t = {
  files : info option String.Table.t;
}

let create () = {files = String.Table.create ()}

let compute_line_starts text =
  let starts = ref [0] in
  String.iteri text ~f:(fun i c ->
      if Char.equal c '\n' then starts := (i + 1) :: !starts);
  Array.of_list_rev !starts

let info t fname =
  Hashtbl.find_or_add t.files fname ~default:(fun () ->
      match In_channel.read_all fname with
      | text -> Some {text; lines = compute_line_starts text}
      | exception _ -> None)

let line_text t ~file n =
  match info t file with
  | None -> None
  | Some {text; lines} ->
    let count = Array.length lines in
    if n < 1 || n > count then None
    else
      let s = lines.(n - 1) in
      (* `lines.(n)` is the offset just past the terminator for line
         `n`, so the content stops at the newline; the final line runs
         to end-of-text. *)
      let e = if n < count then lines.(n) - 1 else String.length text in
      let e = Int.max s e in
      (* Drop a trailing CR so CRLF files underline correctly. *)
      let e = if e > s && Char.equal text.[e - 1] '\r' then e - 1 else e in
      Some (String.sub text ~pos:s ~len:(e - s))

let pos t (p : Lexing.position) =
  let line = Int.max 1 p.Lexing.pos_lnum in
  let col0 = Int.max 0 (p.pos_cnum - p.pos_bol) in
  let byte = match info t p.pos_fname with
    | Some {lines; _} when line <= Array.length lines ->
      lines.(line - 1) + col0
    | _ -> Int.max 0 p.pos_cnum in
  Location.create_pos_exn ~byte ~line ~column:(col0 + 1)

let file_name (p : Lexing.position) =
  if String.is_empty p.Lexing.pos_fname then "<input>" else p.pos_fname

let location_of t (startp : Lexing.position) (endp : Lexing.position) =
  let file = file_name startp in
  let start = pos t startp in
  let end_ = pos t endp in
  (* A single token never spans two source files. If some pathological
     position pair would make `start` follow `end_` by byte, collapse
     to a zero-width range rather than raise. *)
  match Location.create ~file ~start ~end_ with
  | Error _ -> Location.create_exn ~file ~start ~end_:start
  | Ok loc -> loc
