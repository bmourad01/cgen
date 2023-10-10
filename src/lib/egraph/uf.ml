(* Union-find: the greatest data structure since sliced bread. *)

type t = Id.t Vec.t

let create () = Vec.create ()

let fresh t : Id.t =
  let id : Id.t = Vec.length t in
  Vec.push t id;
  id

let parent t (id : Id.t) = Vec.unsafe_get t id
let set_parent t (id : Id.t) p = Vec.unsafe_set t id p

(* Perform path compression while looking up the canonical ID. *)
let rec find t (id : Id.t) =
  let p = parent t id in
  if id <> p then
    let g = parent t p in
    set_parent t id g;
    find t g
  else p

(* Canonicalize towards lower (older) IDs. *)
let union t r1 r2 =
  let r1 = find t r1 in
  let r2 = find t r2 in
  let r1, r2 = min r1 r2, max r1 r2 in
  if r1 <> r2 then set_parent t r2 r1
