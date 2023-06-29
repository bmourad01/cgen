(* "Parse" an expression tree into the e-graph. *)

open Core
open Common

let (@.) = Fn.compose

let prov t a op args =
  let n : enode = N (op, args) in
  let id = add_enode t n in
  update_provenance t id a;
  n, id

let rec pure t : Exp.pure -> (enode * id) = function
  | Palloc (a, n) ->
    prov t a (Oalloc n) []
  | Pbinop (a, b, l, r) ->
    let _, l = pure t l in
    let _, r = pure t r in
    prov t a (Obinop b) [l; r]
  | Pbool b ->
    let n : enode = N (Obool b, []) in
    n, add_enode t n
  | Pcall (a, ty, f, args, vargs) ->
    let _, f = global t f in
    let args = List.map args ~f:(snd @. pure t) in
    let vargs = List.map vargs ~f:(snd @. pure t) in
    let args = add_enode t @@ N (Ocallargs, args) in
    let vargs = add_enode t @@ N (Ocallargs, vargs) in
    prov t a (Ocall ty) [f; args; vargs]
  | Pdouble d ->
    let n : enode = N (Odouble d, []) in
    n, add_enode t n
  | Pint (i, ty) ->
    let n : enode = N (Oint (i, ty), []) in
    n, add_enode t n
  | Pload (a, ty, x) ->
    let _, x = pure t x in
    prov t a (Oload ty) [x]
  | Psel (a, ty, c, y, n) ->
    let _, c = pure t c in
    let _, y = pure t y in
    let _, n = pure t n in
    prov t a (Osel ty) [c; y; n]
  | Psingle s ->
    let n : enode = N (Osingle s, []) in
    n, add_enode t n
  | Psym (s, o) ->
    let n : enode = N (Osym (s, o), []) in
    n, add_enode t n
  | Punop (a, u, x) ->
    let _, x = pure t x in
    prov t a (Ounop u) [x]
  | Pvar x ->
    let n : enode = N (Ovar x, []) in
    n, add_enode t n

and global t : Exp.global -> (enode * id) = function
  | Gaddr a ->
    let n : enode = N (Oaddr a, []) in
    n, add_enode t n
  | Gpure p -> pure t p
  | Gsym s ->
    let n : enode = N (Osym (s, 0), []) in
    n, add_enode t n

let local t : Exp.local -> (enode * id) = function
  | l, args ->
    let args = List.map args ~f:(snd @. pure t) in
    let n : enode = N (Olocal l, args) in
    n, add_enode t n

let dst t : Exp.dst -> (enode * id) = function
  | Dglobal g -> global t g
  | Dlocal l -> local t l

let exp t : exp -> id = function
  | Ebr (c, y, n) ->
    let _, c = pure t c in
    let _, y = dst t y in
    let _, n = dst t n in
    add_enode t @@ N (Obr, [c; y; n])
  | Ecall (f, args, vargs) ->
    let _, f = global t f in
    let args = List.map args ~f:(snd @. pure t) in
    let vargs = List.map vargs ~f:(snd @. pure t) in
    let args = add_enode t @@ N (Ocallargs, args) in
    let vargs = add_enode t @@ N (Ocallargs, vargs) in
    add_enode t @@ N (Ocall0, [f; args; vargs])
  | Ejmp d ->
    let _, d = dst t d in
    add_enode t @@ N (Ojmp, [d])
  | Eret x ->
    let _, x = pure t x in
    add_enode t @@ N (Oret, [x])
  | Eset (x, y) ->
    let _, y = pure t y in
    add_enode t @@ N (Oset x, [y])
  | Estore (ty, v, x) ->
    let _, v = pure t v in
    let _, x = pure t x in
    add_enode t @@ N (Ostore ty, [v; x])
  | Esw (ty, i, d, tbl) ->
    let _, i = pure t i in
    let _, d = local t d in
    let tbl = List.map tbl ~f:(fun (i, l) ->
        let _, l = local t l in
        add_enode t @@ N (Otbl i, [l])) in
    add_enode t @@ N (Osw ty, i :: d :: tbl)
