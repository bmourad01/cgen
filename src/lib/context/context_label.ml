open Core
open Context_common

let init = Int63.(succ (Obj.magic Label.pseudoexit : t))

let fresh = M.{
    run = fun ~reject:_ ~accept s ->
      let l = (Obj.magic s.nextlabel : Label.t) in
      accept l {s with nextlabel = Int63.succ s.nextlabel}
  }
