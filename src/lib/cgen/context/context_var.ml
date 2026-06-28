open Core
open Context_common

type t = Var.t

let fresh = {
  M.run = fun ~reject:_ ~accept s ->
    let x = Var.of_int_unsafe s.state.nextvar in
    let state = {s.state with nextvar = s.state.nextvar + 1} in
    accept x {s with state}
}

let with_allocator f = {
  M.run = fun ~reject ~accept s ->
    let r = ref s.state.nextvar in
    let alloc () =
      let v = !r in
      incr r;
      Var.of_int_unsafe v in
    match f ~alloc with
    | Error e -> reject e
    | Ok result ->
      let state = {s.state with nextvar = !r} in
      accept result {s with state}
}
