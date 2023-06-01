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
  Label.Tree.iter ctx.elts ~f:(fun ~key ~data ->
      if not @@ Hashtbl.mem ctx.exp key then match data with
        | `blk b -> ignore @@ Builder.of_ctrl ctx b
        | `insn (i, b, _) -> ignore @@ Builder.of_insn ctx i b);
  Ok ()

let map_exp ctx l ~f = Hashtbl.change ctx.exp l ~f:(function
    | Some e -> Some (f e)
    | None -> None)

let map ctx ~f = Hashtbl.mapi_inplace ctx.exp
    ~f:(fun ~key ~data -> f key data)

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

let reify_to_fn ctx fn =
  let+ env = reify_fn ctx fn in
  Func.blks fn |> Seq.map ~f:(fun b ->
      let label = Blk.label b in
      let insns = Blk.insns b |> Seq.map ~f:(fun i ->
          let label = Insn.label i in
          match Label.Tree.find env.func label with
          | Some `insn o -> Insn.create o ~label
          | Some `ctrl _ -> assert false
          | None -> i) in
      let ctrl = match Label.Tree.find env.func label with
        | Some `insn _ -> assert false
        | Some `ctrl c -> c
        | None -> Blk.ctrl b in
      Blk.create ()
        ~args:(Blk.args b |> Seq.to_list)
        ~insns:(Seq.to_list insns)
        ~ctrl ~label) |>
  Seq.to_list |> Func.update_blks fn
