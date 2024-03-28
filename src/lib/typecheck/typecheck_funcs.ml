(* Checking function definitions. *)

open Core
open Graphlib.Std
open Regular.Std
open Virtual
open Typecheck_common

module Insns = Typecheck_insns
module Ctrls = Typecheck_ctrls

let not_pseudo = Fn.non Label.is_pseudo

let blk_args =
  let* fn = getfn and* blk = getblk and* env = getenv in
  let* env, _ =
    let init = env, Var.Set.empty in
    Blk.args blk |> M.Seq.fold ~init ~f:(fun (env, seen) x ->
        if Set.mem seen x then
          M.failf "Duplicate argument %a for block %a in function $%s"
            Var.pp x Label.pp (Blk.label blk) (Func.name fn) ()
        else
          let*? _ = Env.typeof_var fn x env in
          !!(env, Set.add seen x)) in
  updenv env

let rec check_blk doms rpo blks seen l =
  let* blk = match Label.Tree.find blks l with
    | Some blk -> !!blk
    | None ->
      let* fn = getfn in
      M.failf "Invariant broken in function $%s: block %a is missing"
        (Func.name fn) Label.pp l () in
  let* () = M.update @@ fun ctx -> {ctx with blk = Some blk} in
  let* () = blk_args in
  let* () = Insns.go seen in
  let* () = Ctrls.go blks @@ Blk.ctrl blk in
  let rpn = Hashtbl.find_exn rpo in
  Tree.children doms l |> Seq.filter ~f:not_pseudo |> Seq.to_list |>
  List.sort ~compare:(fun a b -> compare (rpn a) (rpn b)) |>
  M.List.iter ~f:(check_blk doms rpo blks seen)

let make_rpo cfg start =
  let rpo = Label.Table.create () in
  Graphlib.reverse_postorder_traverse (module Cfg) cfg ~start |>
  Seq.iteri ~f:(fun i l -> Hashtbl.set rpo ~key:l ~data:i);
  rpo

let typ_of_typ_arg env = function
  | #Type.basic as b -> Ok (b :> Type.t)
  | `name n ->
    Env.typeof_typ n env |>
    Or_error.map ~f:(fun t -> (t :> Type.t))

let args =
  let* env = getenv and* fn = getfn in
  let* env, _ =
    let init = env, Var.Set.empty in
    Func.args fn |> M.Seq.fold ~init ~f:(fun (env, seen) (x, t) ->
        if Set.mem seen x then
          M.failf "Duplicate argument %a for function $%s"
            Var.pp x (Func.name fn) ()
        else
          let*? t = typ_of_typ_arg env t in
          let*? env = Env.add_var fn x t env in
          !!(env, Set.add seen x)) in
  updenv env

let slots =
  let* env = getenv and* fn = getfn in
  let t = (Target.word (Env.target env) :> Type.t) in
  let* env, _ =
    let init = env, Var.Set.empty in
    Func.slots fn |> Seq.map ~f:Slot.var |>
    M.Seq.fold ~init ~f:(fun (env, seen) x ->
        if Set.mem seen x then
          M.failf "Duplicate slot %a in function $%s"
            Var.pp x (Func.name fn) ()
        else
          let*? env = Env.add_var fn x t env in
          !!(env, Set.add seen x)) in
  updenv env

let check_entry_inc fn cfg =
  let l = Func.entry fn in
  Cfg.Node.preds l cfg |>
  Seq.filter ~f:(Fn.non Label.is_pseudo) |>
  Seq.length |> function
  | n when n > 0 ->
    M.failf "Entry block %a of function $%s contains %d \
             incoming edges, expected 0"
      Label.pp l (Func.name fn) n ()
  | _ -> !!()

let add m =
  let* init = getenv in
  let* env = Module.funs m |> M.Seq.fold ~init ~f:(fun env fn ->
      M.lift_err @@ Env.add_fn fn env) in
  updenv env

let check fn =
  let* () = M.update @@ fun ctx -> {ctx with fn = Some fn} in
  let* () = args in
  let* () = slots in
  (* Be aware of duplicate labels for instructions. *)
  let seen = Label.Hash_set.create () in
  let*? blks = try Ok (Func.map_of_blks fn) with
    | Invalid_argument msg -> Or_error.error_string msg in
  let cfg = Cfg.create fn in
  let* () = check_entry_inc fn cfg in
  let start = Label.pseudoentry in
  (* We will traverse the blocks according to the dominator tree
     so that we get the right ordering for definitions. *)
  let doms = Graphlib.dominators (module Cfg) cfg start in
  (* However, it requires us to visit children of each node in
     the tree according to the reverse postorder traversal. *)
  check_blk doms (make_rpo cfg start) blks seen @@ Func.entry fn
