open Core

type proc = {
  code   : Shexp_process.Exit_status.t;
  stdout : string;
  stderr : string;
}

let run cmd args =
  let open Shexp_process in
  let open Shexp_process.Infix in
  eval @@
  with_temp_file ~prefix:"stdout" ~suffix:".log" @@ fun stdout_file ->
  with_temp_file ~prefix:"stderr" ~suffix:".log" @@ fun stderr_file ->
  stdout_to stdout_file @@
  stderr_to stderr_file @@
  run_exit_status cmd args >>= fun code ->
  return {
    code;
    stdout = In_channel.read_all stdout_file;
    stderr = In_channel.read_all stderr_file;
  }
