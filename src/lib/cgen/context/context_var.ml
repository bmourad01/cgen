open Core
open Context_common

type t = Var.t

let fresh = {
  M.run = fun ~reject:_ ~accept s ->
    let x = s.state.nextvar in
    let state = {s.state with nextvar = Int63.succ s.state.nextvar} in
    accept (Obj.magic x : t) {s with state}
}

let with_allocator f = {
  M.run = fun ~reject ~accept s ->
    let r = ref s.state.nextvar in
    let alloc () =
      let v = !r in
      Int63.incr r;
      (Obj.magic v : t) in
    match f ~alloc with
    | Error e -> reject e
    | Ok result ->
      let state = {s.state with nextvar = !r} in
      accept result {s with state}
}
