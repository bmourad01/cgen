open Core
open Common

type cost = child:(id -> int) -> enode -> int

(* We'll use an intermediate data structure to extract back to our real
   expression tree representation .*)
type ext = E of Label.t option * Enode.op * ext list

let rec pp_ext ppf = function
  | E (_, op, args) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)" Enode.pp_op op
      (Format.pp_print_list ~pp_sep pp_ext) args

let pps_ext () e = Format.asprintf "%a" pp_ext e

type t = {
  eg          : egraph;
  cost        : cost;
  table       : (int * enode) Id.Table.t;
  memo        : ext Id.Table.t;
  mutable ver : int;
  mutable sat : bool;
}

let init eg ~cost = {
  eg;
  cost;
  table = Id.Table.create ();
  memo = Id.Table.create ();
  ver = eg.ver;
  sat = false;
}

let id_cost t id = match Hashtbl.find t.table @@ find t.eg id with
  | None -> failwithf "Couldn't calculate cost for node id %a" Id.pps id ()
  | Some (c, _) -> c

let has_cost t n =
  Enode.children n |> List.for_all ~f:(Hashtbl.mem t.table)

let node_cost t n =
  if not @@ has_cost t n then None
  else Some (t.cost ~child:(id_cost t) n, n)

(* Find the least-expensive term. *)
let best_term t ns =
  Vec.fold ns ~init:None ~f:(fun acc n ->
      node_cost t n |> Option.merge acc
        ~f:(fun ((c1, _) as a) ((c2, _) as b) ->
            if c2 < c1 then b else a))

(* Saturate the cost table. *)
let rec saturate t (cs : classes) =
  t.sat <- true;
  Hashtbl.iteri cs ~f:(fun ~key:id ~data:ns ->
      match Hashtbl.find t.table id, best_term t ns with
      | None, Some term ->
        Hashtbl.set t.table ~key:id ~data:term;
        t.sat <- false
      | Some (x, _), Some ((y, _) as term) when y < x ->
        Hashtbl.set t.table ~key:id ~data:term;
        t.sat <- false
      | _ -> ());
  if not t.sat then saturate t cs

(* Check if the underlying e-graph has been updated. If so, we should
   re-compute the costs for each node. *)
let check t = if t.ver <> t.eg.ver then begin
    Hashtbl.clear t.table;
    Hashtbl.clear t.memo;
    t.ver <- t.eg.ver;
    t.sat <- false;
  end

open O.Let

let prov t id = Hashtbl.find t.eg.provenance.src id

(* Extract to our intermediate form and cache the results. *)
let rec extract_aux t id =
  let id = find t.eg id in
  match Hashtbl.find t.memo id with
  | Some _ as e -> e
  | None ->
    let* _, n = Hashtbl.find t.table id in
    let+ cs = Enode.children n |> O.List.map ~f:(extract_aux t) in
    let e = E (prov t id, Enode.op n, cs) in
    Hashtbl.set t.memo ~key:id ~data:e;
    e

let rec pure = function
  (* Only canonical forms are accepted. *)
  | E (a, Oalloc n, []) -> Some (Exp.Palloc (a, n))
  | E (a, Obinop b, [l; r]) ->
    let+ l = pure l and+ r = pure r in
    Exp.Pbinop (a, b, l, r)
  | E (_, Obool b, []) -> Some (Exp.Pbool b)
  | E (a, Ocall t, [f; args; vargs]) ->
    let+ f = global f
    and+ args = callargs args
    and+ vargs = callargs vargs in
    Exp.Pcall (a, t, f, args, vargs)
  | E (_, Odouble d, []) -> Some (Exp.Pdouble d)
  | E (_, Oint (i, t), []) -> Some (Exp.Pint (i, t))
  | E (a, Oload t, [x]) ->
    let+ x = pure x in
    Exp.Pload (a, t, x)
  | E (a, Osel t, [c; y; n]) ->
    let+ c = pure c and+ y = pure y and+ n = pure n in
    Exp.Psel (a, t, c, y, n)
  | E (_, Osingle s, []) -> Some (Exp.Psingle s)
  | E (_, Osym (s, n), []) -> Some (Exp.Psym (s, n))
  | E (a, Ounop u, [x]) ->
    let+ x = pure x in
    Exp.Punop (a, u, x)
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

let extract_exn t l = match Hashtbl.find t.eg.provenance.dst l with
  | None -> None
  | Some id ->
    let id = find t.eg id in
    check t;
    if not t.sat then saturate t @@ eclasses t.eg;
    match extract_aux t id with
    | None ->
      invalid_argf "Couldn't extract term for label %a (id %a)"
        Label.pps l Id.pps id ()
    | Some e -> match exp e with
      | Some _ as e -> e
      | None ->
        invalid_argf
          "Term for label %a (id %a) is not well-formed: %a"
          Label.pps l Id.pps id pps_ext e ()

let extract t l = Or_error.try_with @@ fun () -> extract_exn t l
