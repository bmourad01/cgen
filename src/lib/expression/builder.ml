open Core
open Regular.Std
open Virtual
open Common

(* The worklist keeps track of the dependencies that the
   algorithm should attempt to resolve. It also helps us
   construct the dependency graph on the fly. *)
module Worklist : sig
  type t

  val empty : t
  val is_empty : t -> bool
  val remove : t -> Var.t -> t
  val mem : t -> Var.t -> bool
  val singleton : Var.t -> Label.t -> t
  val add : t -> Var.t -> Label.t -> t
  val graph : t -> Label.t -> Var.t -> Deps.t -> Deps.t
end = struct
  type t = Label.Set.t Var.Map.t

  let empty = Var.Map.empty
  let is_empty = Map.is_empty
  let remove = Map.remove
  let mem = Map.mem

  let singleton x l =
    Var.Map.singleton x @@ Label.Set.singleton l

  let add w x l = Map.update w x ~f:(function
      | None -> Label.Set.singleton l
      | Some s -> Set.add s l)

  let graph w src x g =
    Map.find w x |> Option.value_map ~default:g ~f:(fun s ->
        Set.fold s ~init:g ~f:(fun g dst ->
            let e = Deps.Edge.create src dst x in
            Deps.Edge.insert e g))
end

let operand (o : operand) w l = match o with
  | `bool f     -> Pbool f, w
  | `int (i, t) -> Pint (i, t), w
  | `float f    -> Psingle f, w
  | `double d   -> Pdouble d, w
  | `sym (s, o) -> Psym (s, o), w
  | `var v      -> Pvar v, Worklist.add w v l

let operands os w l =
  List.fold_right os ~init:([], w) ~f:(fun o (os, w) ->
      let o, w = operand o w l in
      o :: os, w)

let global (g : Virtual.global) w l = match g with
  | `addr a -> Gaddr a, w
  | `sym s  -> Gsym s, w
  | `var v  -> Gpure (Pvar v), Worklist.add w v l

let local (loc : Virtual.local) w l = match loc with
  | `label (lbl, args) ->
    let args, w = operands args w l in
    (lbl, args), w

let dst (d : Virtual.dst) w l = match d with
  | #Virtual.global as g ->
    let g, w = global g w l in
    Dglobal g, w
  | #Virtual.local as loc ->
    let loc, w = local loc w l in
    Dlocal loc, w

let table tbl w l =
  let tbl, w =
    Ctrl.Table.enum tbl |>
    Seq.fold ~init:([], w) ~f:(fun (tbl, w) (i, loc) ->
        let loc, w = local loc w l in
        (i, loc) :: tbl, w) in
  List.rev tbl, w

let update ctx l ((w, xs) as acc) x f =
  (* Fail if we've already seen this variable. *)
  if Set.mem xs x then
    raise @@ Occurs_failed (x, Some l);
  if Worklist.mem w x then
    let w' = ref @@ Worklist.remove w x in
    (* Assume that the current bound expression is the same. *)
    if not @@ Hashtbl.mem ctx.pure x then begin
      let w, p = f !w' in
      (* Fail early if we re-introduce the same variable. *)
      if Worklist.mem w x then
        raise @@ Occurs_failed (x, Some l);
      Hashtbl.set ctx.pure ~key:x ~data:p;
      w' := w;
    end;
    ctx.deps <- Worklist.graph w l x ctx.deps;
    !w', Set.add xs x
  else acc

(* Accumulate the results of an instruction. *)
let accum ctx acc i =
  let l = Insn.label i in
  let go = update ctx l acc in
  match Insn.op i with
  | `bop (x, o, a, b) -> go x @@ fun w ->
    let a, w = operand a w l in
    let b, w = operand b w l in
    w, Pbinop (l, o, a, b)
  | `uop (x, o, a) -> go x @@ fun w ->
    let a, w = operand a w l in
    w, Punop (l, o, a)
  | `sel (x, t, c, y, n) -> go x @@ fun w ->
    let c, w = Pvar c, Worklist.add w c l in
    let y, w = operand y w l in
    let n, w = operand n w l in
    w, Psel (l, t, c, y, n)
  | `call (Some (x, t), f, args, vargs) -> go x @@ fun w ->
    let f, w = global f w l in
    let args, w = operands args w l in
    let vargs, w = operands vargs w l in
    w, Pcall (l, t, f, args, vargs)
  | `alloc (x, n) -> go x @@ fun w -> w, Palloc (l, n)
  | `load (x, t, a) -> go x @@ fun w ->
    let a, w = operand a w l in
    w, Pload (l, t, a)
  | _ -> acc

(* Kill the variables that appear in the arguments of the block.
   This is the point where we can no longer represent their data
   dependencies as an expression tree.

   Note that this could be a result of a "diamond" property in
   the CFG, not necessarily a loop.
*)
let killed blk w =
  Blk.args blk |> Seq.map ~f:fst |>
  Seq.fold ~init:w ~f:Worklist.remove

let different_insn l i = Label.(l <> Insn.label i)

let subseq blk l ss =
  if Label.(l <> Blk.label blk) then
    Seq.drop_while_option ss ~f:(different_insn l) |>
    Option.value_map ~default:Seq.empty ~f:snd
  else ss

let insns ctx blk l w xs =
  let w, xs =
    Blk.insns blk ~rev:true |> subseq blk l |>
    Seq.fold ~init:(w, xs) ~f:(accum ctx) in
  killed blk w, xs

(* Next blocks to visit. *)
let nexts ctx blk bs =
  Cfg.Node.preds (Blk.label blk) ctx.cfg |>
  Seq.filter_map ~f:(fun l ->
      if Label.is_pseudo l || Set.mem bs l
      then None else match Label.Tree.find ctx.elts l with
        | Some `blk b -> Some b
        | Some _ | None -> None)

let initq blk l w =
  blk, l, w, Label.Set.empty, Var.Set.empty

(* Traverse the data dependencies. *)
let traverse ctx blk l w =
  if not @@ Worklist.is_empty w then
    let q = Stack.singleton @@ initq blk l w in
    while not @@ Stack.is_empty q do
      let blk, l, w, bs, xs = Stack.pop_exn q in
      let w, xs = insns ctx blk l w xs in
      if not @@ Worklist.is_empty w then
        let bs = Set.add bs @@ Blk.label blk in
        nexts ctx blk bs |> Seq.iter ~f:(fun blk ->
            Stack.push q (blk, Blk.label blk, w, bs, xs))
    done

let run ctx blk l f =
  let w, e = f () in
  traverse ctx blk l w;
  let e = Subst.subst ctx e in
  Hashtbl.set ctx.exp ~key:l ~data:e;
  e

let of_ctrl ctx blk =
  let l = Blk.label blk in
  let go = run ctx blk l in
  match Blk.ctrl blk with
  | `hlt -> Ehlt
  | `jmp d -> go @@ fun () ->
    let d, w = dst d Worklist.empty l in
    w, Ejmp d
  | `br (c, y, n) -> go @@ fun () ->
    let c, w = Pvar c, Worklist.singleton c l in
    let y, w = dst y w l in
    let n, w = dst n w l in
    w, Ebr (c, y, n)
  | `ret None -> Eret None
  | `ret (Some x) -> go @@ fun () ->
    let x, w = operand x Worklist.empty l in
    w, Eret (Some x)
  | `sw (t, v, d, tbl) -> go @@ fun () ->
    let v, w = match v with
      | `var x -> Pvar x, Worklist.singleton x l
      | `sym (s, n) -> Psym (s, n), Worklist.empty in
    let d, w = local d w l in
    let tbl, w = table tbl w l in
    w, Esw (t, v, d, tbl)

let of_insn ctx i blk =
  let l = Insn.label i in
  let go = run ctx blk l in
  match Insn.op i with
  | `bop (x, o, a, b) -> go @@ fun () ->
    let a, w = operand a Worklist.empty l in
    let b, w = operand b w l in
    w, Eset (x, Pbinop (l, o, a, b))
  | `uop (x, o, a) -> go @@ fun () ->
    let a, w = operand a Worklist.empty l in
    w, Eset (x, Punop (l, o, a))
  | `sel (x, t, c, y, n) -> go @@ fun () ->
    let y, w = operand y (Worklist.singleton c l) l in
    let n, w = operand n w l in
    w, Eset (x, Psel (l, t, Pvar c, y, n))
  | `call (Some (x, t), f, args, vargs) -> go @@ fun () ->
    let f, w = global f Worklist.empty l in
    let args, w = operands args w l in
    let vargs, w = operands vargs w l in
    w, Eset (x, Pcall (l, t, f, args, vargs))
  | `alloc (x, n) -> Eset (x, Palloc (l, n))
  | `load (x, t, a) -> go @@ fun () ->
    let a, w = operand a Worklist.empty l in
    w, Eset (x, Pload (l, t, a))
  | `call (None, f, args, vargs) -> go @@ fun () ->
    let f, w = global f Worklist.empty l in
    let args, w = operands args w l in
    let vargs, w = operands vargs w l in
    w, Ecall (f, args, vargs)
  | `store (t, v, a) -> go @@ fun () ->
    let v, w = operand v Worklist.empty l in
    let a, w = operand a w l in
    w, Estore (t, v, a)
  | `vaarg (x, t, y) -> Evaarg (x, t, y)
  | `vastart x -> Evastart x
