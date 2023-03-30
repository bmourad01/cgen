open Core
open Cgen

let test_target = Target.create ()
    ~name:"test"
    ~word:`i64
    ~little:true

exception Failed of Error.t

let try_ f = try Context.return @@ f () with
  | Failed err -> Context.fail err

let pass f = fun x -> match f x with
  | Error err -> raise @@ Failed err
  | Ok x -> x

let comp filename =
  let open Context.Syntax in
  let* target = Context.target in
  let* m = Parse.Virtual.from_file filename in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_unreachable_blks.run in
  let*? env = Typecheck.run m ~target in
  let* m = try_ @@ fun () ->
    Virtual.Module.map_funs m ~f:(pass @@ Passes.Ssa.run env) in
  Format.printf "%a\n%!" Virtual.Module.pp m;
  !!()

let () =
  let args = Sys.get_argv () in
  Context.init test_target |>
  Context.run (comp args.(1)) |>
  Or_error.iter_error ~f:(Format.eprintf "%a\n%!" Error.pp)
