open Core
open Graphlib.Std
open Monads.Std
open Regular.Std
open Virtual

include Common
include Eval
include Free_vars
include Labels
include Subst

let try_ f = try f () with
  | Occurs_failed (x, None) ->
    E.failf "Occurs check failed for variable %a" Var.pp x ()
  | Occurs_failed (x, Some l) ->
    E.failf "Occurs check failed for variable %a at instruction %a"
      Var.pp x Label.pp l ()

let get ctx l = try_ @@ fun () ->
  match Hashtbl.find ctx.exp l with
  | Some e -> Ok e
  | None -> match resolve ctx l with
    | Some `blk b -> Ok (Builder.of_ctrl ctx b)
    | Some `insn (i, b, _) -> Ok (Builder.of_insn ctx i b)
    | None -> E.failf "Label %a not found" Label.pp l ()

let fill ctx = try_ @@ fun () ->
  Hashtbl.iteri ctx.elts ~f:(fun ~key ~data ->
      if not @@ Hashtbl.mem ctx.exp key then match data with
        | `blk b -> ignore @@ Builder.of_ctrl ctx b
        | `insn (i, b, _) -> ignore @@ Builder.of_insn ctx i b);
  Ok ()

let map_exp ctx l ~f =
  let open Context.Syntax in
  match Hashtbl.find ctx.exp l with
  | None -> !!()
  | Some e ->
    let+ e = Updater.run ctx l @@ f e in
    Hashtbl.set ctx.exp ~key:l ~data:e

let map ctx ~f =
  let open Context.Syntax in
  Hashtbl.to_alist ctx.exp |>
  Context.List.iter ~f:(fun (l, e) ->
      let+ e = Updater.run ctx l @@ f l e in
      Hashtbl.set ctx.exp ~key:l ~data:e)

module Reify = Reify

open E.Let

let reify ?(init = Reify.empty) ctx l =
  let* e = get ctx l in
  Reify.run ctx l e ~init

let reify_fn ctx fn =
  Func.blks fn |> E.Seq.fold ~init:Reify.empty ~f:(fun init b ->
      let l = Blk.label b in
      let* e = get ctx l in
      let* init = Reify.run ctx l e ~init in
      Blk.insns b |> E.Seq.fold ~init ~f:(fun init i ->
          let l = Insn.label i in
          let* e = get ctx l in
          Reify.run ctx l e ~init))

(* Free variables of some element. *)
type 'a fv = 'a -> Var.Set.t

type news = {
  stk : insn Stack.t;
  mem : Var.Hash_set.t;
}

let create_news () = {
  stk = Stack.create ();
  mem = Var.Hash_set.create ();
}

(* The free variable must:

   1. Be a temporary we generated in the context.
   2. Not have already been committed to the updated function.
   3. Not already have been visited in its basic block.
*)
let valid news ctx x =
  match Hashtbl.find ctx.t2l x with
  | None -> None
  | Some l when Hashtbl.mem ctx.elts l -> None
  | Some l -> match Hash_set.strict_add news.mem x with
    | Error _ -> None
    | Ok () -> Some l

let rec collect : 'a. news -> ctx -> Reify.env -> 'a fv -> 'a -> 'a =
  fun news ctx env fv x ->
  Set.to_sequence (fv x) |>
  Seq.filter_map ~f:(valid news ctx) |>
  Seq.iter ~f:(fun src ->
      match Label.Tree.find env.func src with
      | Some `insn o ->
        Stack.push news.stk @@
        collect news ctx env Insn.free_vars @@
        Insn.create ~label:src o
      | Some `ctrl _ -> assert false
      | None -> ());
  x

(* pre: the stack should form a reverse topological ordering *)
let insert news ctx blk init =
  Stack.fold news.stk ~init ~f:(fun insns i ->
      let key = Insn.label i in
      let data = `insn (i, blk, Hashtbl.find ctx.l2t key) in
      Hashtbl.set ctx.elts ~key ~data;
      i :: insns)

let reify_to_fn ctx fn =
  let+ env = reify_fn ctx fn in
  Func.blks fn |> Seq.map ~f:(fun b ->
      let label = Blk.label b in
      let news = create_news () in
      let ctrl = match Label.Tree.find env.func label with
        | Some `insn _ -> assert false
        | Some `ctrl c -> collect news ctx env Ctrl.free_vars c
        | None -> Blk.ctrl b in
      let insns =
        Blk.insns b ~rev:true |>
        Seq.fold ~init:[] ~f:(fun acc i ->
            let label = Insn.label i in
            match Label.Tree.find env.func label with
            | Some `insn o ->
              let i = Insn.create o ~label in
              collect news ctx env Insn.free_vars i :: acc
            | Some `ctrl _ -> assert false
            | None -> i :: acc) in
      Blk.create ()
        ~args:(Blk.args b |> Seq.to_list)
        ~insns:(insert news ctx b insns)
        ~ctrl ~label) |>
  Seq.to_list |> Func.update_blks fn
