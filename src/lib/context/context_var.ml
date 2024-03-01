open Core
open Context_common

let fresh = M.{
    run = fun ~reject:_ ~accept s ->
      let x = Var_internal.temp s.nextvar in
      accept (Obj.magic x : Var.t) {
        s with nextvar = Int63.succ s.nextvar
      }
  }
