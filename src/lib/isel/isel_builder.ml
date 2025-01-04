open Core
open Regular.Std
open Graphlib.Std
open Virtual.Abi
open Isel_common

let type' ty = (ty :> [Type.basic | `flag])

let infer_ty_binop : Insn.binop -> [Type.basic | `flag] = function
  | `add t
  | `div t
  | `mul t
  | `rem t
  | `sub t -> type' t
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
  | `xor t -> type' t
  | #Virtual.Insn.cmp -> `flag

let infer_ty_unop : Insn.unop -> [Type.basic | `flag] = function
  | `neg t
  | `copy t -> type' t
  | `clz t
  | `ctz t
  | `not_ t
  | `popcnt t
  | `flag t
  | `ftosi (_, t)
  | `ftoui (_, t)
  | `itrunc t
  | `sext t
  | `zext t -> type' t
  | `ifbits t -> type' t
  | `fext t
  | `fibits t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) -> type' t

let new_var t x ty =
  let id = new_node ~ty:(type' ty) t @@ N (Ovar x, []) in
  Hashtbl.set t.vars ~key:x ~data:id

module Make(M : Context.Machine)(C : Context_intf.S) = struct
  open C.Syntax

  module I = M.Isel(C)
  module R = M.Reg
  module Rv = M.Regvar

  let operand' o = (o :> [Virtual.operand | `reg of R.t])

  let reg t r = match R.of_string r with
    | Some r -> !!r
    | None ->
      C.failf
        "In Isel_builder.reg: invalid register %s in function $%s"
        r (Func.name t.fn) ()

  let var t x = match Hashtbl.find t.vars x with
    | Some id -> !!id
    | None ->
      C.failf
        "In Isel_builder.var: unbound variable %a in function $%s"
        Var.pp x (Func.name t.fn) ()

  let typeof_operand t : Virtual.operand -> [Type.basic | `flag] C.t = function
    | `bool _ -> !!`flag
    | `int (_, t) -> !!(type' t)
    | `float _ -> !!`f32
    | `double _ -> !!`f64
    | `sym _ -> !!(type' t.word)
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
      !!(new_node ~ty:(type' ti) t @@ N (Oint (i, ti), []))
    | `float f ->
      !!(new_node ~ty:`f32 t @@ N (Osingle f, []))
    | `double d ->
      !!(new_node ~ty:`f64 t @@ N (Odouble d, []))
    | `sym (s, o) ->
      !!(new_node ~ty:(type' t.word) t @@ N (Osym (s, o), []))
    | `var x -> var t x

  let operands t = C.List.map ~f:(operand t)

  let global t : Virtual.global -> id C.t = function
    | `addr a ->
      !!(new_node ~ty:(type' t.word) t @@ N (Oaddr a, []))
    | `sym (s, o) ->
      !!(new_node ~ty:(type' t.word) t @@ N (Osym (s, o), []))
    | `var x -> var t x

  let blkargs t l args = match Label.Tree.find t.blks l with
    | None ->
      C.failf
        "In Isel_builder.blkargs: missing block for label %a in function $%s"
        Label.pp l (Func.name t.fn) ()
    | Some b ->
      let args' = Seq.to_list @@ Blk.args b in
      match List.zip args' args with
      | Unequal_lengths ->
        C.failf "In Isel_builder.blkargs: unequal lengths for arguments to \
                 block %a in function $%s (got %d, expected %d)"
          Label.pp l (Func.name t.fn) (List.length args') (List.length args) ()
      | Ok moves ->
        C.List.map moves ~f:(fun (x, a) ->
            let* ty = typeof_operand t a in
            I.move (Rv.var x) ty (operand' a))
        >>| List.concat

  let local t : Virtual.local -> id C.t = function
    | `label (l, args) ->
      (* TODO: what do we do with the instructions? *)
      let* _moves = blkargs t l args in
      !!(new_node t @@ N (Olocal l, []))

  let dst t : Virtual.dst -> id C.t = function
    | #Virtual.global as g -> global t g
    | #Virtual.local as l -> local t l

  let insn t i = match Insn.op i with
    | `bop (x, o, a, b) ->
      let* a = operand t a in
      let+ b = operand t b in
      let id = new_node ~ty:(infer_ty_binop o) t @@ N (Obinop o, [a; b]) in
      Hashtbl.set t.vars ~key:x ~data:id;
    | `uop (x, o, a) ->
      let+ a = operand t a in
      let id = new_node ~ty:(infer_ty_unop o) t @@ N (Ounop o, [a]) in
      Hashtbl.set t.vars ~key:x ~data:id
    | `sel (x, ty, c, y, n) ->
      let* c = var t c in
      let* y = operand t y in
      let+ n = operand t n in
      let id = new_node ~ty:(type' ty) t @@ N (Osel ty, [c; y; n]) in
      Hashtbl.set t.vars ~key:x ~data:id
    | `call (ret, _f, _args) ->
      (* TODO *)
      List.iter ret ~f:(fun (x, ty, _) -> new_var t x ty);
      !!()
    | `load (x, ty, _a) ->
      (* TODO *)
      new_var t x ty;
      !!()
    | `store (_ty, _v, _a) ->
      (* TODO *)
      !!()
    | `regcopy (x, ty, _r) ->
      (* TODO *)
      new_var t x ty;
      !!()
    | `regstore (_r, _a) ->
      (* TODO *)
      !!()
    | `regassign (_r, _a) ->
      (* TODO *)
      !!()
    | `stkargs x ->
      (* TODO *)
      new_var t x t.word;
      !!()

  let ctrl t = function
    | `hlt ->
      (* TODO *)
      !!()
    | `jmp d ->
      (* TODO *)
      let* d = dst t d in
      let _id = new_node t @@ N (Ojmp, [d]) in
      !!()
    | `br (c, y, n) ->
      (* TODO *)
      let* c = var t c in
      let* y = dst t y in
      let* n = dst t n in
      let _id = new_node t @@ N (Obr, [c; y; n]) in
      !!()
    | `ret rets ->
      (* TODO *)
      let* _moves = C.List.map rets ~f:(fun (r, a) ->
          let* r = reg t r in
          let* ty = typeof_operand t a in
          I.move (Rv.reg r) ty (operand' a))
        >>| List.concat in
      let _id = new_node t @@ N (Oret, []) in
      !!()
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
      ctrl t @@ Blk.ctrl b

  let enqueue t l q = try
      let cmp a b = compare (t.rpo b) (t.rpo a) in
      Tree.children t.dom l |>
      Seq.to_list |> List.sort ~compare:cmp |>
      List.iter ~f:(Stack.push q);
      !!()
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
