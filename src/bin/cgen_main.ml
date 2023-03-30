open Core
open Cgen

module Test_target = struct
  let r0 = Target.Reg.r64 ~name:"r0"
  let r1 = Target.Reg.r64 ~name:"r1"
  let r2 = Target.Reg.r64 ~name:"r2"
  let r3 = Target.Reg.r64 ~name:"r3"

  let d0 = Target.Reg.r64 ~name:"d0"
  let d1 = Target.Reg.r64 ~name:"d1"
  let d2 = Target.Reg.r64 ~name:"d2"
  let d3 = Target.Reg.r64 ~name:"d3"

  let sp = Target.Reg.r64 ~name:"sp"

  let cf = Target.Reg.r1 ~name:"cf"
  let sf = Target.Reg.r1 ~name:"sf"
  let zf = Target.Reg.r1 ~name:"zf"
  let vf = Target.Reg.r1 ~name:"vf"

  let t = Target.create ()
      ~name:"test"
      ~word:`i64
      ~little:true
      ~flag:[cf; sf; zf; vf]
      ~fp:[d0; d1; d2; d3]
      ~gpr:[r0; r1; r2; r3]
      ~sp
end

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
  Context.init Test_target.t |>
  Context.run (comp args.(1)) |>
  Or_error.iter_error ~f:(Format.eprintf "%a\n%!" Error.pp)
