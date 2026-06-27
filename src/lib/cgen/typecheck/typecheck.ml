open Core
open Virtual

include Typecheck_common

module Funcs = Typecheck_funcs
module Datas = Typecheck_datas
module Types = Typecheck_types

let go m =
  let* () = Types.add m in
  let* () = Datas.add m in
  let* () = Funcs.add m in
  let* () = Module.data m |> M.Seq.iter ~f:Datas.check in
  let* () = Module.funs m |> M.Seq.iter ~f:Funcs.check in
  !!()

let reject e = Error e
let accept _ _ = Ok ()

let check m ~target = (go m).run {
    env = Env.create target;
    fn = None;
    blk = None;
    ins = None;
  } ~reject ~accept
