open Core
open Context_common

let set k v = {
  M.run = fun ~reject:_ ~accept s ->
    accept () {s with local = Dict.set s.local k v}
} [@@inline]

let get k = {
  M.run = fun ~reject:_ ~accept s -> accept (Dict.find s.local k) s
} [@@inline]

let get' k ~default = {
  M.run = fun ~reject:_ ~accept s ->
    Fn.flip accept s @@ match Dict.find s.local k with
    | None -> default
    | Some v -> v
} [@@inline]

let get_err k = {
  M.run = fun ~reject ~accept s ->
    match Dict.find s.local k with
    | Some v -> accept v s
    | None -> reject @@ Error.createf
        "Context_local: key %s is not present"
        (Format.asprintf "%a" Dict.pp_tag k)
} [@@inline]

let erase k = {
  M.run = fun ~reject:_ ~accept s ->
    accept () {s with local = Dict.remove s.local k}
} [@@inline]

let with_ f = {
  M.run = fun ~reject ~accept s ->
    (f ()).M.run s ~reject ~accept:(fun x s' ->
        accept x {s' with local = s.local})
} [@@inline]
