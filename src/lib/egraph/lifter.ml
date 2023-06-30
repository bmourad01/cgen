(* "Lift" an expression tree into the e-graph. *)

open Core
open Common

let prov t a op args =
  let id = add_enode t @@ N (op, args) in
  Option.iter a ~f:(update_provenance t id);
  id

let rec pure t : Exp.pure -> id = function
  | Palloc (a, n) -> prov t a (Oalloc n) []
  | Pbinop (a, b, l, r) -> prov t a (Obinop b) [pure t l; pure t r]
  | Pbool b -> add_enode t @@ N (Obool b, [])
  | Pcall (a, ty, f, args, vargs) ->
    let f = global t f in
    let args = add_enode t @@ N (Ocallargs, args' t args) in
    let vargs = add_enode t @@ N (Ocallargs, args' t vargs) in
    prov t a (Ocall ty) [f; args; vargs]
  | Pdouble d -> add_enode t @@ N (Odouble d, [])
  | Pint (i, ty) -> add_enode t @@ N (Oint (i, ty), [])
  | Pload (a, ty, x) -> prov t a (Oload ty) [pure t x]
  | Psel (a, ty, c, y, n) -> prov t a (Osel ty) [pure t c; pure t y; pure t n]
  | Psingle s -> add_enode t @@ N (Osingle s, [])
  | Psym (s, o) -> add_enode t @@ N (Osym (s, o), [])
  | Punop (a, u, x) -> prov t a (Ounop u) [pure t x]
  | Pvar x -> add_enode t @@ N (Ovar x, [])

and args' t = List.map ~f:(pure t)

and global t : Exp.global -> id = function
  | Gaddr a -> add_enode t @@ N (Oaddr a, [])
  | Gpure p -> pure t p
  | Gsym s -> add_enode t @@ N (Osym (s, 0), [])

let local t : Exp.local -> id = function
  | l, args -> add_enode t @@ N (Olocal l, args' t args)

let dst t : Exp.dst -> id = function
  | Dglobal g -> global t g
  | Dlocal l -> local t l

let exp t : exp -> id = function
  | Ebr (c, y, n) -> add_enode t @@ N (Obr, [pure t c; dst t y; dst t n])
  | Ecall (f, args, vargs) ->
    let f = global t f in
    let args = add_enode t @@ N (Ocallargs, args' t args) in
    let vargs = add_enode t @@ N (Ocallargs, args' t vargs) in
    add_enode t @@ N (Ocall0, [f; args; vargs])
  | Ejmp d -> add_enode t @@ N (Ojmp, [dst t d])
  | Eret x -> add_enode t @@ N (Oret, [pure t x])
  | Eset (x, y) -> add_enode t @@ N (Oset x, [pure t y])
  | Estore (ty, v, x) -> add_enode t @@ N (Ostore ty, [pure t v; pure t x])
  | Esw (ty, i, d, tbl) ->
    let tbl = List.map tbl ~f:(fun (i, l) ->
        add_enode t @@ N (Otbl i, [local t l])) in
    add_enode t @@ N (Osw ty, pure t i :: local t d :: tbl)
