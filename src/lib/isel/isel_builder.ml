(* Builds the graph for running the pattern-matching and rewrite
   engine on. *)

open Core
open Regular.Std
open Graphlib.Std
open Virtual.Abi
open Isel_common

let infer_ty_binop : Insn.binop -> ty = function
  | `add t
  | `div t
  | `mul t
  | `rem t
  | `sub t -> (t :> ty)
  | `mulh t
  | `udiv t
  | `umulh t
  | `urem t
  | `and_ t
  | `or_ t
  | `asr_ t
  | `lsl_ t
  | `lsr_ t
  | `rol t
  | `ror t
  | `xor t -> (t :> ty)
  | #Virtual.Insn.cmp -> `flag

let infer_ty_unop : Insn.unop -> ty = function
  | `neg t
  | `copy t -> (t :> ty)
  | `clz t
  | `ctz t
  | `not_ t
  | `popcnt t
  | `flag t
  | `ftosi (_, t)
  | `ftoui (_, t)
  | `itrunc t
  | `sext t
  | `zext t -> (t :> ty)
  | `ifbits t -> (t :> ty)
  | `fext t
  | `fibits t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) -> (t :> ty)

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax

  module R = M.Reg
  module Rv = M.Regvar

  let reg t r = match R.of_string r with
    | Some r -> !!r
    | None ->
      C.failf
        "In Isel_builder.reg: invalid register %s in function $%s"
        r (Func.name t.fn) ()

  let var t x = match Hashtbl.find t.v2id x with
    | Some id -> !!id
    | None ->
      C.failf
        "In Isel_builder.var: unbound variable %a in function $%s"
        Var.pp x (Func.name t.fn) ()

  let new_var ?l t x ty = Hashtbl.find_or_add t.v2id x ~default:(fun () ->
      let id = new_node ?l ~ty t @@ Rv (Rv.var x) in
      Hashtbl.set t.v2id ~key:x ~data:id;
      Hashtbl.set t.id2r ~key:id ~data:(Rv.var x);
      id)

  let word = (Target.word M.target :> ty)

  let typeof_operand t : Virtual.operand -> ty C.t = function
    | `bool _ -> !!`flag
    | `int (_, t) -> !!(t :> ty)
    | `float _ -> !!`f32
    | `double _ -> !!`f64
    | `sym _ -> !!word
    | `var x ->
      let* id = var t x in
      match typeof t id with
      | Some t -> !!t
      | None ->
        C.failf "In Isel_builder.typeof_operand: expected a type for \
                 variable %a in function $%s"
          Var.pp x (Func.name t.fn) ()

  let operand t : Virtual.operand -> id C.t = function
    | `bool b -> !!(new_node ~ty:`flag t @@ N (Obool b, []))
    | `int (i, ti) ->
      !!(new_node ~ty:(ti :> ty) t @@ N (Oint (i, ti), []))
    | `float f ->
      !!(new_node ~ty:`f32 t @@ N (Osingle f, []))
    | `double d ->
      !!(new_node ~ty:`f64 t @@ N (Odouble d, []))
    | `sym (s, o) ->
      !!(new_node ~ty:word t @@ N (Osym (s, o), []))
    | `var x -> var t x

  let operands t = C.List.map ~f:(operand t)

  let global t : Virtual.global -> id C.t = function
    | `addr a ->
      !!(new_node ~ty:word t @@ N (Oaddr a, []))
    | `sym (s, o) ->
      !!(new_node ~ty:word t @@ N (Osym (s, o), []))
    | `var x -> var t x

  let blkargs t l ld args = match Label.Tree.find t.blks ld with
    | None ->
      C.failf
        "In Isel_builder.blkargs: missing block for label %a in function $%s"
        Label.pp ld (Func.name t.fn) ()
    | Some b ->
      let args' = Seq.to_list @@ Blk.args b in
      match List.zip args' args with
      | Unequal_lengths ->
        C.failf "In Isel_builder.blkargs: unequal lengths for arguments to \
                 block %a in function $%s: got %d, expected %d"
          Label.pp ld (Func.name t.fn) (List.length args') (List.length args) ()
      | Ok moves -> C.List.iter moves ~f:(fun (x, a) ->
          let* ty = typeof_operand t a in
          let+ id = operand t a in
          let n = N (Omove, [new_var t x ty; id]) in
          ignore @@ new_node ~l t n)

  let local t l : Virtual.local -> id C.t = function
    | `label (ld, args) ->
      let* () = blkargs t l ld args in
      !!(new_node t @@ N (Olocal ld, []))

  let dst t l : Virtual.dst -> id C.t = function
    | #Virtual.global as g -> global t g
    | #Virtual.local as loc -> local t l loc

  let insn t i =
    let l = Insn.label i in
    match Insn.op i with
    | `bop (x, o, a, b) ->
      let* a = operand t a in
      let+ b = operand t b in
      let n = N (Obinop o, [a; b]) in
      let ty = infer_ty_binop o in
      let bid = new_node ~ty t n in
      Hashtbl.set t.v2id ~key:x ~data:bid;
      Hashtbl.set t.id2r ~key:bid ~data:(Rv.var x)
    | `uop (x, o, a) ->
      let+ a = operand t a in
      let n = N (Ounop o, [a]) in
      let id = new_node ~l ~ty:(infer_ty_unop o) t n in
      Hashtbl.set t.v2id ~key:x ~data:id;
      Hashtbl.set t.id2r ~key:id ~data:(Rv.var x)
    | `sel (x, ty, c, y, n) ->
      let* c = var t c in
      let* y = operand t y in
      let+ n = operand t n in
      let n = N (Osel ty, [c; y; n]) in
      let id = new_node ~l ~ty:(ty :> ty) t n in
      Hashtbl.set t.v2id ~key:x ~data:id;
      Hashtbl.set t.id2r ~key:id ~data:(Rv.var x)
    | `call (ret, f, _args) ->
      (* TODO: passing args *)
      let* f = global t f in
      ignore @@ new_node ~l t @@ N (Ocall, [f]);
      C.List.iter ret ~f:(fun (x, ty, r) ->
          let+ r = reg t r in
          let ty = (ty :> ty) in
          let rid = new_node ~ty t @@ Rv (Rv.reg r) in
          let xid = new_var t x ty in
          let n = N (Omove, [xid; rid]) in
          ignore @@ new_node ~l t n)
    | `load (x, ty, a) ->
      let+ a = operand t a in
      let ty' = (ty :> ty) in
      let n = N (Oload ty, [a]) in
      let lid = new_node ~l ~ty:ty' t n in
      let vid = new_var t x ty' in
      (* TODO: see if we can do a pessimistic alias analysis to forward
         the `Oload` node where this var appears, where possible. *)
      ignore @@ new_node ~l t @@ N (Omove, [vid; lid])
    | `store (ty, v, a) ->
      let* v = operand t v in
      let+ a = operand t a in
      let ty' = (ty :> [Type.basic | `v128]) in
      let n = N (Ostore ty', [v; a]) in
      ignore @@ new_node ~l t n;
    | `regcopy (x, ty, r) ->
      let+ r = reg t r in
      let ty = (ty :> ty) in
      let rid = new_node ~ty t @@ Rv (Rv.reg r) in
      let xid = new_var t x ty in
      let n = N (Omove, [xid; rid]) in
      ignore @@ new_node ~l t n
    | `regstore (r, a) ->
      let* r = reg t r in
      let+ a = operand t a in
      let ty = R.typeof r in
      let rid = new_node ~ty:(ty :> ty) t @@ Rv (Rv.reg r) in
      let n = N (Ostore ty, [rid; a]) in
      ignore @@ new_node ~l t n
    | `regassign (r, a) ->
      let* r = reg t r in
      let* ty = typeof_operand t a in
      let+ a = operand t a in
      let rid = new_node ~ty t @@ Rv (Rv.reg r) in
      let n = N (Omove, [rid; a]) in
      ignore @@ new_node ~l t n
    | `stkargs x ->
      (* TODO: communicate how the stack frame is going to work *)
      let _xid = new_var t x word in
      !!()

  let ctrl t l : ctrl -> unit C.t = function
    | `hlt ->
      !!(ignore @@ new_node ~l t @@ N (Ohlt, []))
    | `jmp d ->
      let+ d = dst t l d in
      ignore @@ new_node ~l t @@ N (Ojmp, [d]);
    | `br (c, y, n) ->
      let* c = var t c in
      let* y = dst t l y in
      let+ n = dst t l n in
      ignore @@ new_node ~l t @@ N (Obr, [c; y; n])
    | `ret rets ->
      let+ () = C.List.iter rets ~f:(fun (r, a) ->
          let* r = reg t r in
          let* ty = typeof_operand t a in
          let+ aid = operand t a in
          let rid = new_node ~ty t @@ Rv (Rv.reg r) in
          ignore @@ new_node ~l t @@ N (Omove, [rid; aid])) in
      ignore @@ new_node ~l t @@ N (Oret, [])
    | `sw (_ty, _i, _d, _tbl) ->
      (* TODO *)
      !!()

  let step t l = match Label.Tree.find t.blks l with
    | None when Label.is_pseudo l -> !!()
    | None ->
      C.failf
        "In Isel_builder.step: missing block for label %a in function $%s"
        Label.pp l (Func.name t.fn) ()
    | Some b ->
      let* () = Blk.insns b |> C.Seq.iter ~f:(insn t) in
      ctrl t (Blk.label b) (Blk.ctrl b)

  let enqueue t l q = try C.return @@
      let cmp a b = compare (t.rpo b) (t.rpo a) in
      Tree.children t.dom l |>
      Seq.to_list |> List.sort ~compare:cmp |>
      List.iter ~f:(Stack.push q)
    with Missing_rpo l ->
      C.failf "In Isel_builder.enqueue: missing RPO number for label %a in function $%s"
        Label.pp l (Func.name t.fn) ()

  let run t =
    let rec loop q = match Stack.pop q with
      | None -> !!()
      | Some l ->
        let* () = step t l in
        let* () = enqueue t l q in
        loop q in
    loop @@ Stack.singleton Label.pseudoentry
end
