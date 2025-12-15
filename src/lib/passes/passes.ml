open Regular.Std
open Virtual
open Context.Syntax

module Abi_loadopt = Abi_loadopt
module Coalesce_slots = Coalesce_slots
module Destructure = Structured.Destructure(Context)
module Egraph_opt = Egraph_opt
module Lower_abi = Lower_abi
module Promote_slots = Promote_slots
module Remove_dead_vars = Remove_dead_vars
module Remove_disjoint_blks = Remove_disjoint_blks
module Resolve_constant_blk_args = Resolve_constant_blk_args
module Sccp = Sccp
module Simplify_cfg = Simplify_cfg
module Sroa = Sroa
module Ssa = Ssa

let destructure m =
  let+ funs =
    Structured.Module.funs m |>
    Context.Seq.map ~f:Destructure.run >>|
    Seq.to_list in
  Virtual.Module.create () ~funs
    ~dict:(Structured.Module.dict m)
    ~typs:(Structured.Module.typs m |> Seq.to_list)
    ~data:(Structured.Module.data m |> Seq.to_list)
    ~name:(Structured.Module.name m)

let initialize m =
  let* target = Context.target in
  let m = Module.map_funs m ~f:Remove_disjoint_blks.run in
  let*? tenv = Typecheck.run m ~target in
  let*? m = Module.map_funs_err m ~f:Ssa.run in
  !!(tenv, m)

let retype tenv m =
  Module.funs m |> Seq.to_list |> Typecheck.update_fns tenv

let optimize tenv m =
  let module Cv = Context.Virtual in
  let*? m = Module.map_funs_err m ~f:Coalesce_slots.run in
  let*? m = Module.map_funs_err m ~f:Resolve_constant_blk_args.run in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let* m = Context.Virtual.Module.map_funs m ~f:Sroa.run in
  let*? m = Module.map_funs_err m ~f:Promote_slots.run in
  let*? tenv = retype tenv m in
  let*? m = Module.map_funs_err m ~f:(Sccp.run tenv) in
  let m = Module.map_funs m ~f:Remove_disjoint_blks.run in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let* m = Context.Virtual.Module.map_funs m ~f:(Simplify_cfg.run tenv) in
  let*? tenv = retype tenv m in
  let* m = Cv.Module.map_funs m ~f:(Egraph_opt.run tenv) in
  let*? tenv = retype tenv m in
  let m = Module.map_funs m ~f:Remove_disjoint_blks.run in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let*? m = Module.map_funs_err m ~f:Resolve_constant_blk_args.run in
  let*? tenv = retype tenv m in
  let m = Module.map_funs m ~f:Remove_disjoint_blks.run in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let* m = Cv.Module.map_funs m ~f:(Simplify_cfg.run tenv) in
  let*? tenv = retype tenv m in
  let*? m = Module.map_funs_err m ~f:Remove_dead_vars.run in
  let*? tenv = retype tenv m in
  !!(tenv, m)

let to_abi tenv m =
  let+ funs =
    Module.funs m |> Seq.to_list |>
    Context.List.map ~f:(Lower_abi.run tenv) in
  Abi.Module.create () ~funs
    ~name:(Module.name m)
    ~dict:(Module.dict m)
    ~data:(Module.data m |> Seq.to_list)

let optimize_abi m =
  let*? m = Abi.Module.map_funs_err m ~f:Coalesce_slots.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Resolve_constant_blk_args.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Remove_dead_vars.run_abi in
  let* m = Context.Virtual.Module.map_funs_abi m ~f:Sroa.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Promote_slots.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Abi_loadopt.run in
  let m = Abi.Module.map_funs m ~f:Remove_disjoint_blks.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Remove_dead_vars.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Coalesce_slots.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Resolve_constant_blk_args.run_abi in
  let*? m = Abi.Module.map_funs_err m ~f:Abi_loadopt.run in
  let*? m = Abi.Module.map_funs_err m ~f:Remove_dead_vars.run_abi in
  let* () = Context.iter_seq_err (Abi.Module.funs m) ~f:Ssa.check_abi in
  !!m

let assert_same_target msg t' =
  let* t = Context.target in
  Context.unless (Target.equal t t') @@ fun () ->
  Context.failf "In %s: expected target %a, got target %a"
    msg Target.pp t Target.pp t' ()

let isel
    (type i r)
    (module M : Machine_intf.S with type Reg.t = r and type Insn.t = i)
    (m : Abi.module_) : (i, r) Pseudo.module_ Context.t =
  let* () = assert_same_target "isel" M.target in
  let module Isel = Isel.Make(M)(Context) in
  let+ funs =
    Abi.Module.funs m |>
    Context.Seq.map ~f:Isel.run >>|
    Seq.to_list in
  Pseudo.Module.create ()
    ~dict:(Abi.Module.dict m)
    ~data:(Abi.Module.data m |> Seq.to_list)
    ~name:(Abi.Module.name m) ~funs

let regalloc
    (type i r)
    (module M : Machine_intf.S with type Reg.t = r and type Insn.t = i)
    (m : (i, r) Pseudo.module_) : (i, r) Pseudo.module_ Context.t =
  let* () = assert_same_target "regalloc" M.target in
  let module RA = Regalloc.IRC(M)(Context) in
  let+ funs =
    Pseudo.Module.funs m |>
    Context.Seq.map ~f:RA.run >>|
    Seq.to_list in
  Pseudo.Module.with_funs m funs

let to_asm ppf m =
  let* (module Machine) = Context.machine in
  let* m = isel (module Machine) m in
  let module Remove_deads = Pseudo_passes.Remove_dead_insns(Machine) in
  let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
  let+ m = regalloc (module Machine) m in
  let m = Pseudo.Module.map_funs m ~f:Machine.Peephole.run in
  let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
  let module Emit = Pseudo_passes.Emit(Machine) in
  Format.fprintf ppf "%a%!" Emit.emit m
