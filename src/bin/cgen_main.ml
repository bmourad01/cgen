open Core
open Regular.Std
open Cgen

module Test_target = struct
  let r0 = Target.Reg.r64 "r0"
  let r1 = Target.Reg.r64 "r1"
  let r2 = Target.Reg.r64 "r2"
  let r3 = Target.Reg.r64 "r3"

  let d0 = Target.Reg.r64 "d0"
  let d1 = Target.Reg.r64 "d1"
  let d2 = Target.Reg.r64 "d2"
  let d3 = Target.Reg.r64 "d3"

  let sp = Target.Reg.r64 "sp"

  let cf = Target.Reg.r1 "cf"
  let sf = Target.Reg.r1 "sf"
  let zf = Target.Reg.r1 "zf"
  let vf = Target.Reg.r1 "vf"

  let t = Target.create ()
      ~name:"test"
      ~word:`i64
      ~little:true
      ~flag:[cf; sf; zf; vf]
      ~fp:[d0; d1; d2; d3]
      ~gpr:[r0; r1; r2; r3]
      ~sp
end

let comp filename =
  let open Context.Syntax in
  let* target = Context.target in
  let* m = Parse.Virtual.from_file filename in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? tenv = Typecheck.run m ~target in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Ssa.run in
  Format.printf "%a\n%!" Virtual.Module.pp m;
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Simplify_cfg.run in
  let* m = Context.Virtual.Module.map_funs m ~f:(Passes.Peephole.run tenv) in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Simplify_cfg.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  Format.printf "=================================================\n%!";
  Format.printf "%a\n%!" Virtual.Module.pp m;
  !!()

let () =
  let args = Sys.get_argv () in
  Context.init Test_target.t |>
  Context.run (comp args.(1)) |>
  Or_error.iter_error ~f:(Format.eprintf "%a\n%!" Error.pp)
