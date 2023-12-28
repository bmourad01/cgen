open Core
open Context_common

let fresh =
  let* s = M.get () in
  let id = s.nextvar in
  let+ () = M.put {s with nextvar = Int63.succ id} in
  let x = Var_internal.temp id in
  (* XXX: this is ugly, but works *)
  (Obj.magic x : Var.t)
