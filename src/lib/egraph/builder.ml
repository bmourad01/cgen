open Core
open Common
open Virtual

let merge_data c l r ~left ~right = match l, r with
  | Some l, Some r -> assert (equal_const l r); c.data <- Some l
  | Some l, None   -> c.data <- Some l; right ()
  | None,   Some r -> c.data <- Some r; left ()
  | None,   None   -> c.data <- None
[@@specialise]

(* The canonical form for merge operations should be biased towards
   node `a`, except when `b` is known to dominate it. *)
let merge_provenance t a b = match provenance t a, provenance t b with
  | None, Some pb ->
    Hashtbl.set t.provenance ~key:a ~data:pb
  | Some pa, Some pb when t.dominance ~parent:pb pa ->
    Hashtbl.set t.provenance ~key:a ~data:pb
  | Some pa, (Some _ | None) ->
    Hashtbl.set t.provenance ~key:b ~data:pa
  | None, None -> ()

let (@.) = Fn.compose

let rec add_enode t n =
  let n = Enode.canonicalize n t.uf in
  find' t @@ match Hashtbl.find t.nodes n with
  | Some id -> id
  | None ->
    t.ver <- t.ver + 1;
    let id = Uf.fresh t.uf in
    let c = eclass t id in
    let x = n, id in
    Vec.push c.nodes n;
    Enode.children n |> List.iter ~f:(fun ch ->
        Vec.push (eclass t ch).parents x);
    Vec.push t.pending x;
    Hashtbl.set t.nodes ~key:n ~data:id;
    merge_analysis t id;
    id

and add_prov t a op args =
  let n : enode = N (op, args) in
  let id = add_enode t n in
  Hashtbl.update t.provenance id ~f:(function
      | Some b when t.dominance ~parent:b a -> b
      | Some _ | None -> a);
  n, id

and add_pure t : _ Exp.pure -> (enode * id) = function
  | Palloc (a, n) ->
    add_prov t a (Oalloc n) []
  | Pbinop (a, b, l, r) ->
    let _, l = add_pure t l in
    let _, r = add_pure t r in
    add_prov t a (Obinop b) [l; r]
  | Pbool b ->
    let n : enode = N (Obool b, []) in
    n, add_enode t n
  | Pcall (a, ty, f, args, vargs) ->
    let _, f = add_global t f in
    let args = List.map args ~f:(snd @. add_pure t) in
    let vargs = List.map vargs ~f:(snd @. add_pure t) in
    let args = add_enode t @@ N (Ocallargs, args) in
    let vargs = add_enode t @@ N (Ocallargs, vargs) in
    add_prov t a (Ocall ty) [f; args; vargs]
  | Pdouble d ->
    let n : enode = N (Odouble d, []) in
    n, add_enode t n
  | Pint (i, ty) ->
    let n : enode = N (Oint (i, ty), []) in
    n, add_enode t n
  | Pload (a, ty, x) ->
    let _, x = add_pure t x in
    add_prov t a (Oload ty) [x]
  | Psel (a, ty, c, y, n) ->
    let _, c = add_pure t c in
    let _, y = add_pure t y in
    let _, n = add_pure t n in
    add_prov t a (Osel ty) [c; y; n]
  | Psingle s ->
    let n : enode = N (Osingle s, []) in
    n, add_enode t n
  | Psym (s, o) ->
    let n : enode = N (Osym (s, o), []) in
    n, add_enode t n
  | Punop (a, u, x) ->
    let _, x = add_pure t x in
    add_prov t a (Ounop u) [x]
  | Pvar x ->
    let n : enode = N (Ovar x, []) in
    n, add_enode t n

and add_global t : _ Exp.global -> (enode * id) = function
  | Gaddr a ->
    let n : enode = N (Oaddr a, []) in
    n, add_enode t n
  | Gpure p -> add_pure t p
  | Gsym s ->
    let n : enode = N (Osym (s, 0), []) in
    n, add_enode t n

and add_local t : _ Exp.local -> (enode * id) = function
  | l, args ->
    let args = List.map args ~f:(snd @. add_pure t) in
    let n : enode = N (Olocal l, args) in
    n, add_enode t n

and add_dst t : _ Exp.dst -> (enode * id) = function
  | Dglobal g -> add_global t g
  | Dlocal l -> add_local t l

and add t : exp -> id = function
  | Ebr (c, y, n) ->
    let _, c = add_pure t c in
    let _, y = add_dst t y in
    let _, n = add_dst t n in
    add_enode t @@ N (Obr, [c; y; n])
  | Ecall (f, args, vargs) ->
    let _, f = add_global t f in
    let args = List.map args ~f:(snd @. add_pure t) in
    let vargs = List.map vargs ~f:(snd @. add_pure t) in
    let args = add_enode t @@ N (Ocallargs, args) in
    let vargs = add_enode t @@ N (Ocallargs, vargs) in
    add_enode t @@ N (Ocall0, [f; args; vargs])
  | Ejmp d ->
    let _, d = add_dst t d in
    add_enode t @@ N (Ojmp, [d])
  | Eret x ->
    let _, x = add_pure t x in
    add_enode t @@ N (Oret, [x])
  | Eset (x, y) ->
    let _, y = add_pure t y in
    add_enode t @@ N (Oset x, [y])
  | Estore (ty, v, x) ->
    let _, v = add_pure t v in
    let _, x = add_pure t x in
    add_enode t @@ N (Ostore ty, [v; x])
  | Esw (ty, i, d, tbl) ->
    let _, i = add_pure t i in
    let _, d = add_local t d in
    let tbl = List.map tbl ~f:(fun (i, l) ->
        let _, l = add_local t l in
        add_enode t @@ N (Otbl i, [l])) in
    add_enode t @@ N (Osw ty, i :: d :: tbl)

and merge t a b =
  let a = find' t a in
  let b = find' t b in
  if Id.(a <> b) then
    let ca = eclass t a in
    let cb = eclass t b in
    let a, b, ca, cb = if rank ca < rank cb
      then b, a, cb, ca else a, b, ca, cb in
    assert Id.(a = Uf.union t.uf a b);
    assert Id.(a = ca.id);
    t.ver <- t.ver + 1;
    Hashtbl.remove t.classes b;
    Vec.append t.pending cb.parents;
    Vec.append ca.nodes cb.nodes;
    Vec.append ca.parents cb.parents;
    merge_data ca ca.data cb.data
      ~left:(fun () -> Vec.append t.analyses ca.parents)
      ~right:(fun () -> Vec.append t.analyses cb.parents);
    merge_provenance t a b;
    merge_analysis t a

and merge_analysis t id = data t id |> Option.iter ~f:(fun d ->
    merge t (add_enode t @@ Enode.of_const d) id)
