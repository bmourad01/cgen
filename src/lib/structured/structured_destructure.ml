open Core
open Regular.Std

module Func = Structured_func
module Stmt = Structured_stmt
module Ltree = Label.Tree

type ctx = {
  name     : string;
  break    : Label.t option; (* `break` continuation *)
  continue : Label.t option; (* `continue` continuation *)
}

type op = Virtual.Insn.op
type blks = Virtual.blk Ltree.t

let rec is_straightline : Stmt.t -> bool = function
  | #Virtual.Insn.op | `nop -> true
  | `seq (s1, s2) -> is_straightline s1 && is_straightline s2
  | _ -> false

module Make(C : Context_intf.S_virtual) = struct
  open C.Syntax

  type k = {
    apply : op list -> blks -> (Label.t * blks) C.t;
  }

  let mk f = {apply = f}

  (* pre: `ops` is accumulated in reverse order *)
  let add_blk label ops ctrl blks =
    let+ insns = C.List.fold ops ~init:[] ~f:(fun acc op ->
        C.Virtual.insn op >>| Fn.flip List.cons acc) in
    let data = Virtual.Blk.create ~label ~insns ~ctrl () in
    Ltree.set blks ~key:label ~data

  module Lower = struct
    type case = Bv.t * Virtual.local

    type sw = {
      arms        : case list;      (* Explicit cases. *)
      default     : Label.t option; (* Default case. *)
      fallthrough : Label.t;        (* Fallthrough continuation. *)
    }

    let local l : Virtual.local = `label (l, [])
    let dst g = (g :> Virtual.dst)
    let dlocal l = dst@@local l

    let cond c = match (c : Stmt.cond) with
      | `var x -> !!(x, None)
      | `cmp (k, l, r) ->
        let+ x = C.Var.fresh in
        let op = `bop (x, (k :> Virtual.Insn.binop), l, r) in
        x, Some op

    let ctrl ct ops blks =
      let* l = C.Label.fresh in
      let+ blks = add_blk l ops ct blks in
      l, blks

    let goto l ops blks = match ops with
      | _ :: _ -> ctrl (`jmp (dlocal l)) ops blks
      | [] -> !!(l, blks)

    (* Main entry point for lowering a statement. Produces a
       continuation. *)
    let rec cont ~ctx s (k : k) : k = match (s : Stmt.t) with
      | #Virtual.Insn.op as op ->
        (* Accumulate a plain instruction. *)
        mk@@fun ops blks -> k.apply (op :: ops) blks
      | `nop -> k
      | `seq (s1, s2) -> seq ~ctx s1 s2 k
      | `ite (c, y, n) -> ite ~ctx c y n k
      | `loop b -> loop ~ctx b k
      | `break -> break ~ctx
      | `continue -> continue ~ctx
      | `sw (i, ty, cs) -> switch ~ctx i ty cs k
      | `label (l, b) -> label ~ctx l b k
      | `goto (#Virtual.global as g) -> mk@@ctrl (`jmp (dst g))
      | `goto (`label l) -> mk@@goto l
      | `hlt -> mk@@ctrl `hlt
      | `ret _ as r -> mk@@ctrl r

    (* Same as `cont`, but we force the continuation right away. *)
    and go ~ctx s k ops blks = (cont ~ctx s k).apply ops blks

    and seq ~ctx s1 s2 (k : k) : k =
      if is_straightline s1 then
        (* Ideal case: continue emitting in the same block. *)
        cont ~ctx s1 @@ cont ~ctx s2 k
      else mk@@fun ops blks ->
        (* Fall back to the naiive lowering. *)
        let* l2, blks = go ~ctx s2 k [] blks in
        go ~ctx s1 (mk@@goto l2) ops blks

    and ite ~ctx c y n (k : k) : k = mk@@fun ops blks ->
      let* c, ops = cond c >>| function
        | c, Some i -> c, i :: ops
        | c, None -> c, ops in
      (* Join point continuation. *)
      let* join, blks = k.apply [] blks in
      (* Lower each branch. *)
      let* ly, blks = go ~ctx y (mk@@goto join) [] blks in
      let* ln, blks = go ~ctx n (mk@@goto join) [] blks in
      (* Branch to either arm. *)
      let ct = `br (c, dlocal ly, dlocal ln) in
      ctrl ct ops blks

    and loop ~ctx b (k : k) : k = mk@@fun ops blks ->
      (* Loop header continuation. *)
      let* h = C.Label.fresh in
      (* Loop exit continuation. *)
      let* break, blks = k.apply [] blks in
      (* Loop body. *)
      let ctx = {ctx with break = Some break; continue = Some h} in
      let* lb, blks = go ~ctx b (mk@@goto h) [] blks in
      let* blks = add_blk h [] (`jmp (dlocal lb)) blks in
      (* Jump to the loop header. *)
      goto h ops blks

    and break ~ctx : k = mk@@fun ops blks ->
      match ctx.break with
      | Some b -> goto b ops blks
      | None ->
        C.failf
          "Destructure: invalid break in function $%s"
          ctx.name ()

    and continue ~ctx : k = mk@@fun ops blks ->
      match ctx.continue with
      | Some c -> goto c ops blks
      | None ->
        C.failf
          "Destructure: invalid continue in function $%s"
          ctx.name ()

    and switch ~ctx i ty cs (k : k) : k = mk@@fun ops blks ->
      (* Switch exit continuation. *)
      let* break, blks = k.apply [] blks in
      let* blks, sw =
        (* Start from the last case so that we can maintain the correct
           fallthrough continuation. *)
        let ctx = {ctx with break = Some break} in
        let sw = {arms = []; default = None; fallthrough = break} in
        C.List.fold_right cs ~init:(blks, sw) ~f:(switch_acc ~ctx) in
      let d = Option.value ~default:break sw.default in
      match sw.arms with
      | [] ->
        (* No explicit cases, so fall through to the default. *)
        goto d ops blks
      | arms ->
        (* Jump to the switch. *)
        let*? tbl = Virtual.Ctrl.Table.create arms ty in
        let ct = `sw (ty, i, local d, tbl) in
        ctrl ct ops blks

    and switch_acc ~ctx c acc = match c with
      | `case (v, c) -> switch_acc_case ~ctx v c acc
      | `default d -> switch_acc_default ~ctx d acc

    (* Normal switch case. *)
    and switch_acc_case ~ctx v c (blks, sw) =
      let+ l, blks = go ~ctx c (mk@@goto sw.fallthrough) [] blks in
      blks, {
        sw with
        fallthrough = l;
        arms = (v, local l) :: sw.arms;
      }

    (* "default" switch case. *)
    and switch_acc_default ~ctx d (blks, sw) =
      match sw.default with
      | None ->
        let+ l, blks = go ~ctx d (mk@@goto sw.fallthrough) [] blks in
        blks, {
          sw with
          fallthrough = l;
          default = Some l;
        }
      | Some _ ->
        C.failf
          "Destructure: duplicate default switch case in function $%s"
          ctx.name ()

    and label ~ctx l b (k : k) : k = mk@@fun ops blks ->
      let* lb, blks = go ~ctx b k [] blks in
      (* Create a block that immediately jumps to the body. *)
      let* blks = add_blk l [] (`jmp (dlocal lb)) blks in
      (* Jump to the label. *)
      goto l ops blks
  end

  let run fn =
    let name = Func.name fn
    and dict = Func.dict fn
    and body = Func.body fn in
    (* If we reach the end of the function and no value is returned,
       then we will emit a trap. Otherwise, it's safe to just emit a
       void return. *)
    let finish = mk@@match Dict.find dict Func.Tag.return with
      | None -> Lower.ctrl @@ `ret None
      | Some _ -> Lower.ctrl `hlt in
    let ctx = {name; break = None; continue = None} in
    let body = Stmt.normalize body in
    let* start, blks = Lower.go ~ctx body finish [] Ltree.empty in
    (* Ensure that the entry block comes first. *)
    let* sb = match Ltree.find blks start with
      | Some b -> !!b
      | None ->
        C.failf
          "Destructure: missing entry block in function $%s"
          name () in
    let blks = sb :: Ltree.(data @@ remove blks start) in
    C.lift_err @@ Virtual.Func.create () ~dict ~blks ~name
      ~slots:(Func.slots fn |> Seq.to_list)
      ~args:(Func.args fn |> Seq.to_list)
end
