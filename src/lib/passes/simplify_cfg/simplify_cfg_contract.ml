(* Contract edges in the CFG when we find blocks with no instructions
   and a single unconditional jump. *)

open Core
open Regular.Std
open Virtual
open Simplify_cfg_common

open O.Let
open O.Syntax

module Lset = Label.Tree_set

type singles = dst Label.Tree.t

type chain =
  | Dest of dst
  | Next of Label.t * Label.t * chain

let can_be_single env l b =
  Label.(l <> env.start) &&
  Seq.is_empty (Blk.insns b)

let singles env : singles =
  Hashtbl.fold env.blks ~init:Label.Tree.empty
    ~f:(fun ~key:l ~data:b m -> match Blk.ctrl b with
        | `jmp d when can_be_single env l b ->
          Label.Tree.set m ~key:l ~data:d
        | _ -> m)

(* Chase down the final destination. *)
let chase ?(local_only = false) (s : singles) l =
  let rec aux l vis =
    let* () = O.guard @@ not @@ Lset.mem vis l in
    Label.Tree.find s l >>= function
    | #global when local_only -> None
    | #global as g -> !!(Dest g)
    | `label (l', _) as loc ->
      match aux l' @@ Lset.add vis l with
      | Some x -> !!(Next (l, l', x))
      | None -> !!(Dest loc) in
  aux l Lset.empty

(* Perform the substitutions on block arguments for the entire chain.

   The final substitution happens when we reach the `Dest` case, at
   which point we return it and it becomes the new destination for
   the block at the beginning of this chain.

   I am mentioning this here because I want to remind myself later
   that this is sound.
*)
let rec eval subst env = function
  | Dest d -> !!(Subst_mapper.map_dst subst d)
  | Next (l, l', x) ->
    let* b = Hashtbl.find env.blks l in
    let* b' = Hashtbl.find env.blks l' in
    let* subst = Subst_mapper.blk_extend subst b b' in
    eval subst env x

let init_subst env l args =
  let* b = Hashtbl.find env.blks l in
  let args' = Seq.to_list @@ Blk.args b in
  match List.zip args' args with
  | Unequal_lengths -> None
  | Ok xs -> match Var.Map.of_alist xs with
    | `Ok m -> !!m
    | `Duplicate_key x ->
      (* This shouldn't happen if we passed the type checker. *)
      failwithf "Couldn't create substitution for block %a: \
                 duplicate var %a" Label.pps l Var.pps x ()

let find_dst env s : dst -> dst option = function
  | #global -> None
  | `label (l, args) ->
    let* subst = init_subst env l args in
    chase s l >>= eval subst env

let find_loc env s : local -> local option = function
  | `label (l, args) ->
    let* subst = init_subst env l args in
    chase s l ~local_only:true >>=
    eval subst env >>| function
    | #global -> assert false
    | #local as l -> l

let map_dst changed env s d = match find_dst env s d with
  | Some x when equal_dst d x -> x
  | Some x -> changed := true; x
  | None -> d

let map_loc changed env s l = match find_loc env s l with
  | Some x when equal_local l x -> x
  | Some x -> changed := true; x
  | None -> l

let contract_blks changed env (s : singles) =
  Hashtbl.map_inplace env.blks ~f:(fun b ->
      let dst = map_dst changed env s in
      let loc = map_loc changed env s in
      Blk.map_ctrl b ~f:(function
          | (`hlt | `ret _) as x -> x
          | `jmp d -> `jmp (dst d)
          | `br (c, y, n) ->
            let y = dst y in
            let n = dst n in
            if equal_dst y n
            then (changed := true; `jmp y)
            else `br (c, y, n)
          | `sw (t, i, d, tbl) ->
            let d = loc d in
            let tbl = Ctrl.Table.map_exn tbl ~f:(fun i l -> i, loc l) in
            sw_hoist_default changed t i d tbl))

let run env =
  let changed = ref false in
  let s = singles env in
  if not @@ Label.Tree.is_empty s then
    contract_blks changed env s;
  !changed
