open Core
open Virtual

include Typecheck_common

module Funcs = Typecheck_funcs
module Datas = Typecheck_datas
module Types = Typecheck_types

(* Main procedure. *)

let check m =
  let* () = Types.add m in
  let* () = Types.check in
  let* () = Datas.add m in
  let* () = Funcs.add m in
  let* () = Module.data m |> M.Seq.iter ~f:Datas.check in
  let* () = Module.funs m |> M.Seq.iter ~f:Funcs.check in
  !!()

let reject e = Error e
let accept _ ctx = Ok ctx.env

let run m ~target = (check m).run {
    env = Env.create target;
    fn = None;
    blk = None;
    ins = None;
  } ~reject ~accept

(* Updating the environment when a function definition is transformed. *)

let remove_fn fn =
  let name = Func.name fn in
  M.update @@ fun ctx -> {
    ctx with env = {
      ctx.env with
      fenv = Map.remove ctx.env.fenv name;
      venv = Map.remove ctx.env.venv name;
    }}

let add_fn fn =
  let* env = getenv in
  let*? env = Env.add_fn fn env in
  updenv env

let update_fn env fn =
  let go =
    let* () = remove_fn fn in
    let* () = add_fn fn in
    let* () = Funcs.check fn in
    !!() in
  go.run {
    env;
    fn = None;
    blk = None;
    ins = None;
  } ~reject ~accept

let update_fns env fns =
  let go =
    let* () = M.List.iter fns ~f:remove_fn in
    let* () = M.List.iter fns ~f:add_fn in
    let* () = M.List.iter fns ~f:Funcs.check in
    !!() in
  go.run {
    env;
    fn = None;
    blk = None;
    ins = None;
  } ~reject ~accept
