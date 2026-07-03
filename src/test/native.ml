open Core
open OUnit2
open Cgen

let output_asm m file =
  let open Context.Syntax in
  let oc = Out_channel.create file in
  let fmt = Format.formatter_of_out_channel oc in
  let+ () = Passes.to_asm fmt m in
  Out_channel.close oc

let compile_c_driver asm driver exe =
  let p = Cgen_utils.Process.run "cc" [asm; driver; "-o"; exe; "-g"; "-fno-omit-frame-pointer"] in
  match p.code with
  | Shexp_process.Exit_status.Exited n ->
    Context.unless (n = 0) @@ fun () ->
    Context.failf "failed to compile C driver program %s (error code %d): %s"
      driver n p.stderr ()
  | Shexp_process.Exit_status.Signaled n ->
    Context.failf "failed to compile C driver program %s (signaled %d): %s"
      driver n p.stderr ()

let run target ~asm ~exe ~driver_c ~driver_output ~build =
  Context.init target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = build in
    let* () = output_asm m asm in
    let+ () = compile_c_driver asm driver_c exe in
    Cgen_utils.Process.run exe []
  end |> function
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err
  | Ok p ->
    begin match p.code with
      | Shexp_process.Exit_status.Exited n ->
        let msg = Format.sprintf
            "Unexpected return code: got %d, expected 0\n\nSTDERR:\n%s\n"
            n p.stderr in
        assert_bool msg (n = 0)
      | Shexp_process.Exit_status.Signaled n ->
        assert_failure @@ Format.sprintf
          "Process signaled %d, expected return code 0\n\nSTDERR:\n%s\n" n p.stderr
    end;
    if Shexp_process.(eval @@ file_exists driver_output) then
      Golden.compare_or_update () ~chop_end:false
        ~expected_file:driver_output ~actual:p.stdout ~fail:assert_failure
