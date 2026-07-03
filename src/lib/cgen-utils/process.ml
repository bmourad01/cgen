open Core

type t = {
  code   : Shexp_process.Exit_status.t;
  stdout : string;
  stderr : string;
}

let run ?stdin prog args =
  let open Shexp_process in
  let open Shexp_process.Infix in
  eval @@
  with_temp_file ~prefix:"cgen-proc-out" ~suffix:".tmp" @@ fun outf ->
  with_temp_file ~prefix:"cgen-proc-err" ~suffix:".tmp" @@ fun errf ->
  let capture stdin_file =
    let proc = run_exit_status prog args in
    let proc =
      Option.value_map stdin_file ~default:proc ~f:(fun f -> stdin_from f proc) in
    stdout_to outf (stderr_to errf proc) >>= fun code ->
    return {
      code;
      stdout = In_channel.read_all outf;
      stderr = In_channel.read_all errf;
    } in
  match stdin with
  | None -> capture None
  | Some data ->
    with_temp_file ~prefix:"cgen-proc-in" ~suffix:".tmp" @@ fun inf ->
    Out_channel.write_all inf ~data;
    capture (Some inf)
