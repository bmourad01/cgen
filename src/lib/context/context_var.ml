open Core
open Context_common

type t = Var.t

let fresh = {
  M.run = fun ~reject:_ ~accept s ->
    let x = Var_internal.temp s.state.nextvar in
    let state = {s.state with nextvar = Int63.succ s.state.nextvar} in
    accept (Obj.magic x : t) {s with state}
}
