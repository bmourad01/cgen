open Core
open Context_common

let set k v = {
  M.run = fun ~reject:_ ~accept s ->
    accept () {s with local = Dict.set s.local k v}
}

let get k = {
  M.run = fun ~reject:_ ~accept s -> accept (Dict.find s.local k) s
}

let get' k ~default = {
  M.run = fun ~reject:_ ~accept s ->
    Fn.flip accept s @@ match Dict.find s.local k with
    | None -> default
    | Some v -> v
}

let get_err k = {
  M.run = fun ~reject ~accept s ->
    match Dict.find s.local k with
    | Some v -> accept v s
    | None -> reject @@ Error.createf
        "Context_local: key %s is not present"
        (Format.asprintf "%a" Dict.pp_tag k)
}

let erase k = {
  M.run = fun ~reject:_ ~accept s ->
    accept () {s with local = Dict.remove s.local k}
}
