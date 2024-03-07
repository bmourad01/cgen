open Context_common

let set k v = M.{
    run = fun ~reject:_ ~accept s ->
      accept () {
        s with local = Dict.set s.local k v
      }
  }

let get k ~default = M.{
    run = fun ~reject:_ ~accept s ->
      let v = match Dict.find s.local k with
        | None -> default
        | Some v -> v in
      accept v s
  }

let erase k = M.{
    run = fun ~reject:_ ~accept s ->
      accept () {
        s with local = Dict.remove s.local k
      }
  }
