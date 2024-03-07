open Core
open Context_common

let init = Int63.(succ (Obj.magic Label.pseudoexit : t))

let fresh = M.{
    run = fun ~reject:_ ~accept s ->
      let l = (Obj.magic s.state.nextlabel : Label.t) in
      accept l {
        s with state = {
          s.state with nextlabel = Int63.succ s.state.nextlabel
        }
      }
  }
