open Core
open Cgen

module Test_target = struct
  let r0 = Target.Reg.r64 ~name:"r0" ~cls:`gpr
  let r1 = Target.Reg.r64 ~name:"r1" ~cls:`gpr
  let r2 = Target.Reg.r64 ~name:"r2" ~cls:`gpr
  let r3 = Target.Reg.r64 ~name:"r3" ~cls:`gpr

  let d0 = Target.Reg.r64 ~name:"d0" ~cls:`fp
  let d1 = Target.Reg.r64 ~name:"d1" ~cls:`fp
  let d2 = Target.Reg.r64 ~name:"d2" ~cls:`fp
  let d3 = Target.Reg.r64 ~name:"d3" ~cls:`fp

  let sp = Target.Reg.r64 ~name:"sp" ~cls:`sp

  let cf = Target.Reg.r1 ~name:"cf" ~cls:`flag
  let sf = Target.Reg.r1 ~name:"sf" ~cls:`flag
  let zf = Target.Reg.r1 ~name:"zf" ~cls:`flag
  let vf = Target.Reg.r1 ~name:"vf" ~cls:`flag

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
