open Core
open Context_common

let init = (Label.pseudoexit :> int) + 1

let fresh = {
  M.run = fun ~reject:_ ~accept s ->
    let l = Label.of_int_unsafe s.state.nextlabel in
    let state = {s.state with nextlabel = s.state.nextlabel + 1} in
    accept l {s with state}
}
