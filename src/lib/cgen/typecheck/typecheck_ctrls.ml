(* Checking control-flow instructions of a block. *)

open Core
open Regular.Std
open Virtual
open Typecheck_common

let unequal_lengths_ctrl l args targs =
  let* fn = getfn and* blk = getblk in
  M.failf "Jump to %a in block %a of function $%s: \
           expected %d arguments, got %d"
    Label.pp l Label.pp (Blk.label blk) (Func.name fn)
    (List.length targs) (List.length args) ()

let check_var_dst v =
  let* env = getenv and* fn = getfn in
  let word = Target.word @@ Env.target env in
  let*? t = Env.typeof_var fn v env in
  M.unless Type.(t = (word :> t)) @@ fun () ->
  M.lift_err @@ unify_fail t (word :> Type.t) v fn

let check_label_dst blks l args =
  let* fn = getfn and* blk = getblk in
  let* b = match Label.Tree.find blks l with
    | Some b -> !!b
    | None ->
      M.failf "Jump destination %a at block %a in function $%s \
               does not exist."
        Label.pp l Label.pp (Blk.label blk) (Func.name fn) () in
  let targs = Seq.to_list @@ Blk.args b in
  match List.zip args targs with
  | Unequal_lengths -> unequal_lengths_ctrl l args targs
  | Ok z -> M.List.iter z ~f:(fun (a, x) ->
      let* env = getenv in
      let* ta = typeof_arg fn env a in
      let*? env = Env.add_var fn x ta env in
      updenv env)

let check_dst blks : dst -> unit t = function
  | `addr _ | `sym _ -> !!()
  | `var v -> check_var_dst v
  | `label (l, args) -> check_label_dst blks l args

let unify_flag_fail_ctrl t v =
  let* fn = getfn and* blk = getblk in
  M.failf "Expected mem type for var %a of jnz in block %a in \
           function $%s, got %a"
    Var.pp v Label.pp (Blk.label blk) (Func.name fn) Type.pp t ()

let unify_fail_void_ret t =
  let* fn = getfn and* blk = getblk in
  M.failf "Failed to unify return types %a and <void> for \
           ret in block %a of function $%s"
    Type.pp t Label.pp (Blk.label blk) (Func.name fn) ()

let unify_fail_ret t1 t2 =
  let* fn = getfn and* blk = getblk in
  M.failf "Failed to unify return types %a and %a for \
           ret in block %a of function $%s"
    Type.pp t1 Type.pp t2 Label.pp (Blk.label blk) (Func.name fn) ()

let ctrl_br blks c t f =
  let* env = getenv and* fn = getfn in
  let*? tc = Env.typeof_var fn c env in
  let* () = M.unless Type.(tc = `flag) @@ fun () ->
    unify_flag_fail_ctrl tc c in
  let* () = check_dst blks t in
  check_dst blks f

let ctrl_ret_none =
  let* env = getenv and* fn = getfn in
  match Func.return fn with
  | Some t -> typeof_type_ret env t >>= unify_fail_void_ret
  | None -> !!()

let ctrl_ret_some r =
  let* env = getenv and* fn = getfn in
  let* tr = typeof_arg fn env r in
  match tr, Func.return fn with
  | t, None -> unify_fail_void_ret t
  | #Type.t as r, Some t ->
    let* t' = typeof_type_ret env t in
    M.unless Type.(r = t') @@ fun () ->
    unify_fail_ret r t'

let sw_unify_fail t t' =
  let* fn = getfn and* blk = getblk in
  M.failf "Expected type %a for index of `sw` instruction in \
           block %a in function $%s, got %a"
    Type.pp t Label.pp (Blk.label blk)
    (Func.name fn) Type.pp t' ()

let check_sw_index t i =
  let m = max_of_imm t in
  M.when_ Bv.(i > m) @@ fun () ->
  let* fn = getfn and* blk = getblk in
  M.failf "In `sw.%a` instruction in block %a in function $%s: \
           index %a_%a does not fit in type %a"
    Type.pp_imm t Label.pp (Blk.label blk) (Func.name fn)
    Bv.pp i Type.pp_imm t Type.pp_imm t ()

let ctrl_sw blks t v d tbl =
  let t' = (t :> Type.t) in
  let* env = getenv and* fn = getfn in
  let*? tv = match v with
    | `var v -> Env.typeof_var fn v env
    | `sym _ -> Ok (Target.word env.target :> Type.t) in
  if Type.(t' = tv) then
    let* () = check_dst blks (d :> dst) in
    Ctrl.Table.enum tbl |> M.Seq.iter ~f:(fun (i, l) ->
        let* () = check_sw_index t i in
        check_dst blks (l :> dst))
  else sw_unify_fail t' tv

let go blks c =
  (* A bit of a hack, but it's a convention that the control
     instruction's label is represented by the block it
     belongs to. *)
  let* () = M.update @@ fun ctx -> match ctx.blk with
    | Some b -> {ctx with ins = Some (Blk.label b)}
    | None -> assert false in
  match (c : ctrl) with
  | `hlt -> !!()
  | `jmp d -> check_dst blks d
  | `br (c, t, f) -> ctrl_br blks c t f
  | `ret None -> ctrl_ret_none
  | `ret (Some r) -> ctrl_ret_some r
  | `sw (t, v, d, tbl) -> ctrl_sw blks t v d tbl
