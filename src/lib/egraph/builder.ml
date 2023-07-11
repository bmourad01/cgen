open Core
open Monads.Std
open Regular.Std
open Virtual
open Common

module E = Monad.Result.Error

exception Occurs_failed of Var.t * Label.t option

(* The state of the expression builder. *)
type t = {
  pure   : Exp.pure Var.Table.t;
  exp    : Exp.t Label.Table.t;
  filled : Id.t Var.Table.t;
}

let init () = {
  pure = Var.Table.create ();
  exp = Label.Table.create ();
  filled = Var.Table.create ();
}

type work = Var.Set.t

(* Lift our tree representation into e-nodes.

   This is a bottom-up process, whereas building the expression trees
   is done top-down.
*)
module Lifter = struct
  let prov eg a op args =
    let id = add_enode eg @@ N (op, args) in
    Option.iter a ~f:(update_provenance eg id);
    id

  let rec pure ?(vs = Var.Set.empty) t eg (p : Exp.pure) : id =
    let pure = pure t eg ~vs in match p with
    | Palloc (a, n) -> prov eg a (Oalloc n) []
    | Pbinop (a, b, l, r) -> prov eg a (Obinop b) [pure l; pure r]
    | Pbool b -> add_enode eg @@ N (Obool b, [])
    | Pdouble d -> add_enode eg @@ N (Odouble d, [])
    | Pint (i, ty) -> add_enode eg @@ N (Oint (i, ty), [])
    | Psel (a, ty, c, y, n) -> prov eg a (Osel ty) [pure c; pure y; pure n]
    | Psingle s -> add_enode eg @@ N (Osingle s, [])
    | Psym (s, o) -> add_enode eg @@ N (Osym (s, o), [])
    | Punop (a, u, x) -> prov eg a (Ounop u) [pure x]
    | Pvar x when Set.mem vs x -> raise @@ Occurs_failed (x, None)
    | Pvar x -> var t eg vs x

  and var t eg vs x = match Hashtbl.find t.filled x with
    | Some id -> id
    | None ->
      let id = match Hashtbl.find t.pure x with
        | None -> add_enode eg @@ N (Ovar x, [])
        | Some p -> pure t eg p ~vs:(Set.add vs x) in
      Hashtbl.set t.filled ~key:x ~data:id;
      id

  and args' ?(vs = Var.Set.empty) t eg = List.map ~f:(pure t eg ~vs)

  and global ?(vs = Var.Set.empty) t eg : Exp.global -> id = function
    | Gaddr a -> add_enode eg @@ N (Oaddr a, [])
    | Gpure p -> pure t eg p ~vs
    | Gsym s -> add_enode eg @@ N (Osym (s, 0), [])

  let local t eg : Exp.local -> id = function
    | l, args -> add_enode eg @@ N (Olocal l, args' t eg args)

  let dst t eg : Exp.dst -> id = function
    | Dglobal g -> global t eg g
    | Dlocal l -> local t eg l

  let exp t eg : exp -> id =
    let pure = pure t eg in
    let dst = dst t eg in function
      | Ebr (c, y, n) -> add_enode eg @@ N (Obr, [pure c; dst y; dst n])
      | Ecall (x, f, args, vargs) ->
        let f = global t eg f in
        let args = add_enode eg @@ N (Ocallargs, args' t eg args) in
        let vargs = add_enode eg @@ N (Ocallargs, args' t eg vargs) in
        let op = match x with
          | Some (x, t) -> Enode.Ocall (x, t)
          | None -> Enode.Ocall0 in
        add_enode eg @@ N (op, [f; args; vargs])
      | Eload (x, t, y) -> add_enode eg @@ N (Oload (x, t), [pure y])
      | Ejmp d -> add_enode eg @@ N (Ojmp, [dst d])
      | Eret x -> add_enode eg @@ N (Oret, [pure x])
      | Eset (x, y) -> add_enode eg @@ N (Oset x, [pure y])
      | Estore (ty, v, x) -> add_enode eg @@ N (Ostore ty, [pure v; pure x])
      | Esw (ty, i, d, tbl) ->
        let tbl = List.map tbl ~f:(fun (i, l) ->
            add_enode eg @@ N (Otbl i, [local t eg l])) in
        add_enode eg @@ N (Osw ty, pure i :: local t eg d :: tbl)
end

let operand (o : operand) w : Exp.pure * work = match o with
  | `bool f     -> Pbool f, w
  | `int (i, t) -> Pint (i, t), w
  | `float f    -> Psingle f, w
  | `double d   -> Pdouble d, w
  | `sym (s, o) -> Psym (s, o), w
  | `var v      -> Pvar v, Set.add w v

let operands os w =
  List.fold_right os ~init:([], w) ~f:(fun o (os, w) ->
      let o, w = operand o w in
      o :: os, w)

let global (g : Virtual.global) w : Exp.global * work = match g with
  | `addr a -> Gaddr a, w
  | `sym s  -> Gsym s, w
  | `var v  -> Gpure (Pvar v), Set.add w v

let local (loc : Virtual.local) w = match loc with
  | `label (lbl, args) ->
    let args, w = operands args w in
    (lbl, args), w

let dst (d : Virtual.dst) w : Exp.dst * work = match d with
  | #Virtual.global as g ->
    let g, w = global g w in
    Dglobal g, w
  | #Virtual.local as loc ->
    let loc, w = local loc w in
    Dlocal loc, w

let table tbl w =
  let tbl, w =
    Ctrl.Table.enum tbl |>
    Seq.fold ~init:([], w) ~f:(fun (tbl, w) (i, loc) ->
        let loc, w = local loc w in
        (i, loc) :: tbl, w) in
  List.rev tbl, w

let update t l ((w, xs) as acc) x f =
  (* Fail if we've already seen this variable. *)
  if Set.mem xs x then
    raise @@ Occurs_failed (x, Some l);
  if Set.mem w x then
    let w' = ref @@ Set.remove w x in
    (* Assume that the current bound expression is the same. *)
    if not @@ Hashtbl.mem t.pure x then begin
      let w, p = f !w' in
      (* Fail early if we re-introduce the same variable. *)
      if Set.mem w x then
        raise @@ Occurs_failed (x, Some l);
      Hashtbl.set t.pure ~key:x ~data:p;
      w' := w;
    end;
    !w', Set.add xs x
  else acc

(* Accumulate the results of an instruction. *)
let accum t acc i =
  let l = Insn.label i in
  let go = update t l acc in
  match Insn.op i with
  | `bop (x, o, a, b) -> go x @@ fun w ->
    let a, w = operand a w in
    let b, w = operand b w in
    w, Pbinop (Some l, o, a, b)
  | `uop (x, o, a) -> go x @@ fun w ->
    let a, w = operand a w in
    w, Punop (Some l, o, a)
  | `sel (x, t, c, y, n) -> go x @@ fun w ->
    let c, w = Exp.Pvar c, Set.add w c in
    let y, w = operand y w in
    let n, w = operand n w in
    w, Psel (Some l, t, c, y, n)
  | `call (None, _, _, _) -> acc
  | `call (Some (x, _), _, _, _) ->
    let w, xs = acc in
    Set.remove w x, xs
  | `alloc (x, n) -> go x @@ fun w -> w, Palloc (Some l, n)
  | `load (x, _, _) ->
    let w, xs = acc in
    Set.remove w x, xs
  | `store _ -> acc
  | `vaarg (x, _, y) ->
    let w, xs = acc in
    let w = Set.remove w x in
    let w = Set.remove w y in
    w, xs
  | `vastart x ->
    let w, xs = acc in
    Set.remove w x, xs

(* Kill the variables that appear in the arguments of the block.
   This is the point where we can no longer represent their data
   dependencies as an expression tree.

   Note that this could be a result of a "diamond" property in
   the CFG, not necessarily a loop.
*)
let killed blk w =
  Blk.args blk |> Seq.map ~f:fst |>
  Seq.fold ~init:w ~f:Set.remove

let different_insn l i = Label.(l <> Insn.label i)

let subseq blk l ss =
  if Label.(l <> Blk.label blk) then
    Seq.drop_while_option ss ~f:(different_insn l) |>
    Option.value_map ~default:Seq.empty ~f:snd
  else ss

let insns t blk l w xs =
  let w, xs =
    Blk.insns blk ~rev:true |> subseq blk l |>
    Seq.fold ~init:(w, xs) ~f:(accum t) in
  killed blk w, xs

(* Next blocks to visit. *)
let nexts (input : Input.t) blk bs =
  Cfg.Node.preds (Blk.label blk) input.cfg |>
  Seq.filter_map ~f:(fun l ->
      if Label.is_pseudo l || Set.mem bs l
      then None else match Hashtbl.find input.tbl l with
        | Some `blk b -> Some b
        | Some _ | None -> None)

let initq blk l w =
  blk, l, w, Label.Set.empty, Var.Set.empty

(* Traverse the data dependencies. *)
let traverse t input blk l w =
  if not @@ Set.is_empty w then
    let q = Stack.singleton @@ initq blk l w in
    while not @@ Stack.is_empty q do
      let blk, l, w, bs, xs = Stack.pop_exn q in
      let w, xs = insns t blk l w xs in
      if not @@ Set.is_empty w then
        let bs = Set.add bs @@ Blk.label blk in
        nexts input blk bs |> Seq.iter ~f:(fun blk ->
            Stack.push q (blk, Blk.label blk, w, bs, xs))
    done

let lift t eg blk l f =
  let w, e = f () in
  traverse t eg.input blk l w;
  Hashtbl.set eg.lbl2id ~key:l ~data:(Lifter.exp t eg e)

let ctrl t eg blk =
  let l = Blk.label blk in
  let go = lift t eg blk l in
  match Blk.ctrl blk with
  | `hlt -> ()
  | `jmp d -> go @@ fun () ->
    let d, w = dst d Var.Set.empty in
    w, Ejmp d
  | `br (c, y, n) -> go @@ fun () ->
    let c, w = Exp.Pvar c, Var.Set.singleton c in
    let y, w = dst y w in
    let n, w = dst n w in
    w, Ebr (c, y, n)
  | `ret None -> ()
  | `ret (Some x) -> go @@ fun () ->
    let x, w = operand x Var.Set.empty in
    w, Eret x
  | `sw (t, v, d, tbl) -> go @@ fun () ->
    let v, w = match v with
      | `var x -> Exp.Pvar x, Var.Set.singleton x
      | `sym (s, n) -> Exp.Psym (s, n), Var.Set.empty in
    let d, w = local d w in
    let tbl, w = table tbl w in
    w, Esw (t, v, d, tbl)

let insn t eg i blk =
  let l = Insn.label i in
  let go = lift t eg blk l in
  match Insn.op i with
  | `bop (x, o, a, b) -> go @@ fun () ->
    let a, w = operand a Var.Set.empty in
    let b, w = operand b w in
    w, Eset (x, Pbinop (Some l, o, a, b))
  | `uop (x, o, a) -> go @@ fun () ->
    let a, w = operand a Var.Set.empty in
    w, Eset (x, Punop (Some l, o, a))
  | `sel (x, t, c, y, n) -> go @@ fun () ->
    let y, w = operand y @@ Var.Set.singleton c in
    let n, w = operand n w in
    w, Eset (x, Psel (Some l, t, Pvar c, y, n))
  | `call (x, f, args, vargs) -> go @@ fun () ->
    let f, w = global f Var.Set.empty in
    let args, w = operands args w in
    let vargs, w = operands vargs w in
    w, Ecall (x, f, args, vargs)
  | `alloc (x, n) -> go @@ fun () ->
    Var.Set.empty, Eset (x, Palloc (Some l, n))
  | `load (x, t, a) -> go @@ fun () ->
    let a, w = operand a Var.Set.empty in
    w, Eload (x, t, a)
  | `store (t, v, a) -> go @@ fun () ->
    let v, w = operand v Var.Set.empty in
    let a, w = operand a w in
    w, Estore (t, v, a)
  | `vaarg _ | `vastart _ -> ()

let try_ f = try f () with
  | Occurs_failed (x, None) ->
    E.failf "Occurs check failed for variable %a" Var.pp x ()
  | Occurs_failed (x, Some l) ->
    E.failf "Occurs check failed for variable %a at instruction %a"
      Var.pp x Label.pp l ()

let run eg = try_ @@ fun () ->
  let t = init () in
  Hashtbl.iter eg.input.tbl ~f:(function
      | `blk b -> ctrl t eg b
      | `insn (i, b, _) -> insn t eg i b);
  Ok ()
