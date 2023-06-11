(* Union-find: the greatest data structure since sliced bread. *)

open Core

type t = Id.t Vec.t

let create () = Vec.create ()

let fresh t : Id.t =
  let id : Id.t = Obj.magic @@ Vec.length t in
  Vec.push t id;
  id

let parent t (id : Id.t) = Vec.unsafe_get t (id :> int)
let set_parent t (id : Id.t) p = Vec.unsafe_set t (id :> int) p
let union t r1 r2 = set_parent t (parent t r2) r1; r1

let rec find t (id : Id.t) =
  let p = parent t id in
  if Id.(id <> p) then
    let g = parent t p in
    set_parent t id g;
    find t g
  else p
