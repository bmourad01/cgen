(* Extract to our more strictly-formed expression tree representation. *)

open Extractor_core
open O.Let

let lbl = function
  | Label l -> Some l
  | Id _ -> None

let rec pure = function
  (* Only canonical forms are accepted. *)
  | E (a, Oalloc n, []) -> Some (Exp.Palloc (lbl a, n))
  | E (a, Obinop b, [l; r]) ->
    let+ l = pure l and+ r = pure r in
    Exp.Pbinop (lbl a, b, l, r)
  | E (_, Obool b, []) -> Some (Exp.Pbool b)
  | E (a, Ocall t, [f; args; vargs]) ->
    let+ f = global f
    and+ args = callargs args
    and+ vargs = callargs vargs in
    Exp.Pcall (lbl a, t, f, args, vargs)
  | E (_, Odouble d, []) -> Some (Exp.Pdouble d)
  | E (_, Oint (i, t), []) -> Some (Exp.Pint (i, t))
  | E (a, Oload t, [x]) ->
    let+ x = pure x in
    Exp.Pload (lbl a, t, x)
  | E (a, Osel t, [c; y; n]) ->
    let+ c = pure c and+ y = pure y and+ n = pure n in
    Exp.Psel (lbl a, t, c, y, n)
  | E (_, Osingle s, []) -> Some (Exp.Psingle s)
  | E (_, Osym (s, n), []) -> Some (Exp.Psym (s, n))
  | E (a, Ounop u, [x]) ->
    let+ x = pure x in
    Exp.Punop (lbl a, u, x)
  | E (_, Ovar x, []) -> Some (Exp.Pvar x)
  (* The rest are rejected. *)
  | E (_, Oaddr _, _)
  | E (_, Oalloc _, _)
  | E (_, Obinop _, _)
  | E (_, Obool _, _)
  | E (_, Obr, _)
  | E (_, Ocall0, _)
  | E (_, Ocall _, _)
  | E (_, Ocallargs, _)
  | E (_, Odouble _, _)
  | E (_, Ojmp, _)
  | E (_, Oint _, _)
  | E (_, Oload _, _)
  | E (_, Olocal _, _)
  | E (_, Oret, _)
  | E (_, Osel _, _)
  | E (_, Oset _, _)
  | E (_, Osingle _, _)
  | E (_, Ostore _, _)
  | E (_, Osw _, _)
  | E (_, Osym _, _)
  | E (_, Otbl _, _)
  | E (_, Ounop _, _)
  | E (_, Ovar _, _) -> None

and callargs = function
  | E (_, Ocallargs, args) -> O.List.map args ~f:pure
  | _ -> None

and global = function
  | E (_, Oaddr a, []) -> Some (Exp.Gaddr a)
  | E (_, Oaddr _, _) -> None
  | E (_, Osym (s, 0), []) -> Some (Exp.Gsym s)
  | E (_, Osym _, _) -> None
  | e ->
    let+ p = pure e in
    Exp.Gpure p

let local l args =
  let+ args = O.List.map args ~f:pure in
  l, args

let dst = function
  | E (_, Olocal l, args) ->
    let+ l = local l args in
    Exp.Dlocal l
  | e ->
    let+ g = global e in
    Exp.Dglobal g

let table = function
  | E (_, Otbl i, [E (_, Olocal l, args)]) ->
    let+ l = local l args in
    i, l
  | _ -> None

let exp = function
  (* Only canonical forms are accepted. *)
  | E (_, Obr, [c; y; n]) ->
    let+ c = pure c and+ y = dst y and+ n = dst n in
    Exp.Ebr (c, y, n)
  | E (_, Ocall0, [f; args; vargs]) ->
    let+ f = global f
    and+ args = callargs args
    and+ vargs = callargs vargs in
    Exp.Ecall (f, args, vargs)
  | E (_, Ojmp, [d]) ->
    let+ d = dst d in
    Exp.Ejmp d
  | E (_, Oret, [x]) ->
    let+ x = pure x in
    Exp.Eret x
  | E (_, Oset x, [y]) ->
    let+ y = pure y in
    Exp.Eset (x, y)
  | E (_, Ostore t, [v; x]) ->
    let+ v = pure v and+ x = pure x in
    Exp.Estore (t, v, x)
  | E (_, Osw t, i :: d :: tbl) ->
    let+ i = pure i
    and+ d = match d with
      | E (_, Olocal l, args) -> local l args
      | _ -> None
    and+ tbl = O.List.map tbl ~f:table in
    Exp.Esw (t, i, d, tbl)
  (* The rest are rejected. *)
  | E (_, Oaddr _, _)
  | E (_, Oalloc _, _)
  | E (_, Obinop _, _)
  | E (_, Obool _, _)
  | E (_, Obr, _)
  | E (_, Ocall0, _)
  | E (_, Ocall _, _)
  | E (_, Ocallargs, _)
  | E (_, Odouble _, _)
  | E (_, Ojmp, _)
  | E (_, Oint _, _)
  | E (_, Oload _, _)
  | E (_, Olocal _, _)
  | E (_, Oret, _)
  | E (_, Osel _, _)
  | E (_, Oset _, _)
  | E (_, Osingle _, _)
  | E (_, Ostore _, _)
  | E (_, Osw _, _)
  | E (_, Osym _, _)
  | E (_, Otbl _, _)
  | E (_, Ounop _, _)
  | E (_, Ovar _, _) -> None
