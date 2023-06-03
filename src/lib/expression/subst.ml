open Core
open Common

(* Keep track of the set of variables we're substituting. If
   we find a cycle in the dependency chain then the function
   is probably not in SSA form. *)
let rec subst_pure ?(vs = Var.Set.empty) ctx e =
  let go = subst_pure ctx ~vs in
  match e with
  | Palloc _ as a -> a
  | Pbinop (l, o, x, y) ->
    Pbinop (l, o, go x, go y)
  | Pbool _ | Pdouble _ | Pint _ | Psingle _ | Psym _ -> e
  | Pcall (l, t, f, args, vargs) ->
    let args = List.map args ~f:go in
    let vargs = List.map vargs ~f:go in
    Pcall (l, t, subst_global ctx f ~vs, args, vargs)
  | Pload (l, t, a) -> Pload (l, t, go a)
  | Psel (l, t, c, y, n) -> Psel (l, t, go c, go y, go n)
  | Punop (l, o, x) -> Punop (l, o, go x)
  | Pvar x when Set.mem vs x -> raise @@ Occurs_failed (x, None)
  | Pvar x as default ->
    Hashtbl.find ctx.pure x |>
    Option.value_map ~default ~f:(continue x vs ctx)

(* Make the full substitution on subterms and cache the results. *)
and continue x vs ctx = function
  | (Palloc _ | Pbool _ | Pdouble _ | Pint _ | Psingle _ | Psym _) as e -> e
  | e when Hash_set.mem ctx.filled x -> e
  | e ->
    let e = subst_pure ctx e ~vs:(Set.add vs x) in
    Hashtbl.set ctx.pure ~key:x ~data:e;
    Hash_set.add ctx.filled x;
    e

and subst_global ?(vs = Var.Set.empty) ctx = function
  | (Gaddr _ | Gsym _) as g -> g
  | Gpure p -> Gpure (subst_pure ctx p ~vs)

let subst_local ctx (l, args) = l, List.map args ~f:(subst_pure ctx)

let subst_dst ctx = function
  | Dglobal g -> Dglobal (subst_global ctx g)
  | Dlocal l -> Dlocal (subst_local ctx l)

let subst_table m = List.map ~f:(fun (i, l) -> i, subst_local m l)

let subst ctx e =
  let pure = subst_pure ctx in
  let dst = subst_dst ctx in
  match e with
  | Ebr (c, y, n) -> Ebr (pure c, dst y, dst n)
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:pure in
    let vargs = List.map vargs ~f:pure in
    Ecall (subst_global ctx f, args, vargs)
  | Ejmp d -> Ejmp (subst_dst ctx d)
  | Eret None as r -> r
  | Eret (Some p) -> Eret (Some (subst_pure ctx p))
  | Eset (x, y) -> Eset (x, subst_pure ctx y ~vs:(Var.Set.singleton x))
  | Estore (t, v, a) -> Estore (t, pure v, pure a)
  | Esw (t, v, d, tbl) ->
    Esw (t, pure v, subst_local ctx d, subst_table ctx tbl)
  | (Ehlt | Evaarg _ | Evastart _) as e -> e
