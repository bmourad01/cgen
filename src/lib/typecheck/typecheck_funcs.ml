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
  let* _ =
    Blk.args blk |> M.Seq.fold ~init:Var.Set.empty
      ~f:(fun seen x -> if Set.mem seen x then
             M.failf "Duplicate argument %a for block %a in function $%s"
               Var.pp x Label.pp (Blk.label blk) (Func.name fn) ()
           else
             (* NB: `x` should be present in the environment due to the order
                in which we traverse the domtree (see `Ctrls.check_label_dst`) *)
             let*? _ = Env.typeof_var fn x env in
             !!(Set.add seen x)) in
  updenv env

let rec check_blk doms blks seen l =
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
  Semi_nca.Tree.children doms l |> Seq.filter ~f:not_pseudo |>
  M.Seq.iter ~f:(check_blk doms blks seen)

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

let check_entry_args fn blks =
  let l = Func.entry fn in
  let* b = match Label.Tree.find blks l with
    | Some b -> !!b
    | None ->
      M.failf "Entry block %a for function $%s not found"
        Label.pp l (Func.name fn) () in
  M.unless (Seq.is_empty @@ Blk.args b) @@ fun () ->
  M.failf "Entry block %a for function $%s must not have any arguments"
    Label.pp l (Func.name fn) ()

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
  let* () = check_entry_args fn blks in
  let start = Label.pseudoentry in
  (* We will traverse the blocks according to the dominator tree
     so that we get the right ordering for definitions. The API
     here guarantees that children are sorted by RPO number. *)
  let doms = Semi_nca.compute (module Cfg) cfg start in
  check_blk doms blks seen @@ Func.entry fn
