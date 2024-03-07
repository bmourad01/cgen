open Core
open Context_common

let fresh = M.{
    run = fun ~reject:_ ~accept s ->
      let x = Var_internal.temp s.state.nextvar in
      accept (Obj.magic x : Var.t) {
        s with state = {
          s.state with nextvar = Int63.succ s.state.nextvar
        }
      }
  }
