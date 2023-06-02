(* The updater is used after transforming an expression, and does
   the following:

   1. Insert fresh labels and variables for new subexpressions,
      which can later be reified into new instructions for the
      function.

   2. Update the dependency graph.
*)

open Core
open Regular.Std
open Graphlib.Std
open Virtual
open Common

open Context.Syntax

let update ctx l ~dep f =
  let+ l, p, x = match l with
    | Some l ->
      let+ p = f l in
      let x = match resolve ctx l with
        | Some `insn (_, _, Some x) -> x
        | _ -> assert false in
      l, p, x
    | None ->
      let* l, x = new_var ctx in
      let+ p = f l in
      let e = Eset (x, p) in
      Hashtbl.set ctx.exp ~key:l ~data:e;
      l, p, x in
  if Label.(l <> dep) then begin
    let e = Deps.Edge.create l dep x in
    ctx.deps <- Deps.Edge.insert e ctx.deps
  end;
  p

let rec pure ctx p ~dep =
  let pure = pure ctx in
  let upd = update ctx ~dep in
  match p with
  | Palloc (l, n) -> upd l @@ fun l ->
    !!(Palloc (Some l, n))
  | Pbinop (l, o, a, b) -> upd l @@ fun l ->
    let+ a = pure a ~dep:l and+ b = pure b ~dep:l in
    Pbinop (Some l, o, a, b)
  | (Pbool _ | Pdouble _ | Pint _ | Psingle _ | Psym _ | Pvar _) as p -> !!p
  | Pcall (l, t, f, args, vargs) -> upd l @@ fun l ->
    let+ f = global ctx f ~dep
    and+ args = Context.List.map args ~f:(pure ~dep:l)
    and+ vargs = Context.List.map vargs ~f:(pure ~dep:l) in
    Pcall (Some l, t, f, args, vargs)
  | Pload (l, t, a) -> upd l @@ fun l ->
    let+ a = pure a ~dep:l in
    Pload (Some l, t, a)
  | Psel (l, t, c, y, n)  -> upd l @@ fun l ->
    let+ c = pure c ~dep:l
    and+ y = pure y ~dep:l
    and+ n = pure n ~dep:l in
    Psel (Some l, t, c, y, n)
  | Punop (l, o, a) -> upd l @@ fun l ->
    let+ a = pure a ~dep:l in
    Punop (Some l, o, a)

and global ctx ~dep = function
  | (Gaddr _ | Gsym _) as g -> !!g
  | Gpure p ->
    let+ p = pure ctx p ~dep in
    Gpure p

let local ctx (l, args) ~dep =
  let+ args = Context.List.map args ~f:(pure ctx ~dep) in
  l, args

let dst ctx ~dep = function
  | Dglobal g ->
    let+ g = global ctx g ~dep in
    Dglobal g
  | Dlocal l ->
    let+ l = local ctx l ~dep in
    Dlocal l

let table ctx ~dep = Context.List.map ~f:(fun (i, l) ->
    let+ l = local ctx l ~dep in
    i, l)

let exp ctx e ~dep =
  let pure = pure ctx ~dep in
  let dst = dst ctx ~dep in
  match e with
  | Ebr (c, y, n) ->
    let+ c = pure c and+ y = dst y and+ n = dst n in
    Ebr (c, y, n)
  | Ecall (f, args, vargs) ->
    let+ f = global ctx f ~dep
    and+ args = Context.List.map args ~f:pure
    and+ vargs = Context.List.map vargs ~f:pure in
    Ecall (f, args, vargs)
  | Ehlt -> !!Ehlt
  | Ejmp d ->
    let+ d = dst d in
    Ejmp d
  | Eret None -> !!(Eret None)
  | Eret (Some x) ->
    let+ x = pure x in
    Eret (Some x)
  | Eset (x, y) ->
    let+ y = pure y in
    Eset (x, y)
  | Estore (t, v, a) ->
    let+ v = pure v and+ a = pure a in
    Estore (t, v, a)
  | Esw (t, i, d, tbl) ->
    let+ i = pure i
    and+ d = local ctx d ~dep
    and+ tbl = table ctx tbl ~dep in
    Esw (t, i, d, tbl)
  | (Evaarg _ | Evastart _) as e -> !!e

(* Remove edges where there is a node that is not reachable from
   the root expression. *)
let check_edge ls e g =
  if Set.mem ls (Deps.Edge.src e)
  && Set.mem ls (Deps.Edge.dst e)
  then g else Deps.Edge.remove e g

(* Update the graph for edges that were implicitly removed when
   the expression was transformed. *)
let remove_old_deps ctx l e =
  let ls = Set.add (Labels.labels e) l in
  ctx.deps <- fst @@ Graphlib.depth_first_search (module Deps) ctx.deps
      ~rev:true ~start:l ~init:(ctx.deps, false)
      ~start_tree:(fun n (g, _) -> g, Set.mem ls n)
      ~enter_edge:(fun _ e -> function
          | g, true -> check_edge ls e g, true
          | s -> s)

(* Remove nodes from the graph that have no edges. *)
let remove_unused_deps ctx =
  Deps.nodes ctx.deps |> Seq.iter ~f:(fun l ->
      if Deps.Node.degree l ctx.deps <= 0 then
        ctx.deps <- Deps.Node.remove l ctx.deps)

let run ctx l e =
  let+ e = exp ctx e ~dep:l in
  remove_old_deps ctx l e;
  remove_unused_deps ctx;
  e
