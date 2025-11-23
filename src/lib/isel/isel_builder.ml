(* Builds the graph for running the pattern-matching and rewrite
   engine on. *)

open Core
open Regular.Std
open Virtual.Abi
open Isel_common

module Slot = Virtual.Slot

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

  let var t x = match getvar t x with
    | Some id -> !!id
    | None ->
      C.failf
        "In Isel_builder.var: unbound variable %a in function $%s"
        Var.pp x (Func.name t.fn) ()

  let newvar = newvar ~f:Rv.var
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

  let constant t : Virtual.const -> Id.t = function
    | `bool b ->
      new_node ~ty:`flag t @@ N (Obool b, [])
    | `int (i, ti) ->
      new_node ~ty:(ti :> ty) t @@ N (Oint (i, ti), [])
    | `float f ->
      new_node ~ty:`f32 t @@ N (Osingle f, [])
    | `double d ->
      new_node ~ty:`f64 t @@ N (Odouble d, [])
    | `sym (s, o) ->
      new_node ~ty:word t @@ N (Osym (s, o), [])

  let operand t : Virtual.operand -> Id.t C.t = function
    | #Virtual.const as c -> !!(constant t c)
    | `var x -> var t x

  let operands t = C.List.map ~f:(operand t)

  let global t : Virtual.global -> Id.t C.t = function
    | `addr a ->
      !!(new_node ~ty:word t @@ N (Oaddr a, []))
    | `sym (s, o) ->
      !!(new_node ~ty:word t @@ N (Osym (s, o), []))
    | `var x -> var t x

  let zip_blkargs t ld args = match Label.Tree.find t.blks ld with
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
      | Ok moves -> !!moves

  (* XXX: can we do better than this kludge?

     This is meant to avoid creating duplicate instructions
     by making the ID of the var unique, but it might cost
     us some opportunities to make better selection decisions.
  *)
  let operand' t a =
    let+ ty = typeof_operand t a in
    match a with
    | #Virtual.const as c -> ty, constant t c
    | `var x -> ty, new_node ~ty t @@ Rv (Rv.var (regcls ty) x)

  (* From the paper:

     "Tilting at windmills with Coq: formal verification of a
     compilation algorithm for parallel moves" (2008)

     by L. Rideau, B. P. Serpette, & X. Leroy
  *)
  let windmill t l moves =
    let moves = Array.of_list moves in
    let n = Array.length moves in
    let status = Array.create ~len:n `to_move in
    let subst = Var.Table.create () in
    let rewrite = function
      | `var v as default ->
        Hashtbl.find subst v |>
        Option.value ~default
      | src -> src in
    let emit ?i dst src =
      let+ ty, id = operand' t @@ rewrite src in
      let n = N (Omove, [newvar t dst ty; id]) in
      ignore @@ new_node ~l t n;
      Option.iter i ~f:(fun i -> status.(i) <- `moved) in
    let rec move_one i =
      let dst, src = moves.(i) in
      match src with
      | #Virtual.const ->
        (* Not a var: emit normally. *)
        emit ~i dst src
      | `var v when Var.(dst = v) ->
        (* Ignore redundant moves. *)
        !!(status.(i) <- `moved)
      | `var _ ->
        status.(i) <- `being_moved;
        let* () = dfs i dst in
        emit ~i dst src
    and dfs i dst = Seq.range 0 n |> C.Seq.iter ~f:(fun j ->
        (* Find a child whose `src` depends on `dst`. *)
        C.unless (i = j) @@ fun () ->
        match rewrite @@ snd moves.(j) with
        | #Virtual.const -> !!()
        | `var v when Var.(dst <> v) -> !!()
        | `var v as src' -> match status.(j) with
          | `moved -> !!()
          | `to_move -> move_one j
          | `being_moved ->
            (* Found a cycle, so we need to use a fresh
               temporary. *)
            let* tmp = C.Var.fresh in
            let+ () = emit tmp src' in
            (* Any future mention of `v` will refer to `tmp`. *)
            Hashtbl.set subst ~key:v ~data:(`var tmp)) in
    (* Entry point: consider all pending moves. *)
    Seq.range 0 n |> C.Seq.iter ~f:(fun i ->
        match status.(i) with
        | `to_move -> move_one i
        | _ -> !!())

  let blkargs ?(br = false) t l ld args =
    zip_blkargs t ld args >>= function
    | [] -> !!None
    | moves ->
      (* If applicable, make a new administrative block for the
         moves to be inserted into. *)
      let* l', ld' = if br then
          let+ l' = C.Label.fresh in
          addextra t l l';
          l', l'
        else !!(l, ld) in
      let+ () = windmill t l' moves in
      if br then begin
        let lid = new_node t @@ N (Olocal ld, []) in
        ignore @@ new_node ~l:l' t @@ N (Ojmp, [lid])
      end;
      Some ld'

  let local ?(br = false) t l : Virtual.local -> (Label.t * Id.t) C.t = function
    | `label (ld, args) ->
      let+ ld' = blkargs ~br t l ld args >>| function
        | Some ld' -> ld'
        | None -> ld in
      ld', new_node t @@ N (Olocal ld', [])

  let dst ?(br = false) t l : Virtual.dst -> Id.t C.t = function
    | #Virtual.global as g -> global t g
    | #Virtual.local as loc -> local ~br t l loc >>| snd

  let eval_binop o a b = match a, b with
    | `int (a, _), `int (b, _) ->
      (Eval.binop_int o a b :> Virtual.const option)
    | `float a, `float b ->
      (Eval.binop_single o a b :> Virtual.const option)
    | `double a, `double b ->
      (Eval.binop_double o a b :> Virtual.const option)
    | _ -> None

  let eval_unop o = function
    | `int (a, ty) ->
      (Eval.unop_int o a ty :> Virtual.const option)
    | `float a ->
      (Eval.unop_single o a :> Virtual.const option)
    | `double a ->
      (Eval.unop_double o a :> Virtual.const option)
    | _ -> None

  let binop t l x o a b =
    let ty = infer_ty_binop o in
    let+ id = match eval_binop o a b with
      | Some c -> !!(constant t c)
      | None ->
        let* a = operand t a in
        let+ b = operand t b in
        let n = N (Obinop o, [a; b]) in
        new_node ~ty t n in
    let r = Rv.var (regcls ty) x in
    let rid = new_node ~ty t @@ Rv r in
    ignore @@ new_node ~l t @@ N (Omove, [rid; id]);
    setvar t x id;
    setrv t id r

  let unop t l x o a =
    let* () = match o with
      | `uitof _ when not M.supports_uitof ->
        C.failf
          "In Isel_builder.unop: uitof is not supported by target %a"
          Target.pp M.target ()
      | _ -> !!() in
    let ty = infer_ty_unop o in
    let+ id = match eval_unop o a with
      | Some c -> !!(constant t c)
      | None -> match o with
        | `copy _ -> operand t a (* copy propagation *)
        | _ ->
          let+ a = operand t a in
          let n = N (Ounop o, [a]) in
          new_node ~ty t n in
    let r = Rv.var (regcls ty) x in
    let rid = new_node ~ty t @@ Rv r in
    ignore @@ new_node ~l t @@ N (Omove, [rid; id]);
    setvar t x id;
    setrv t id r

  let sel t l x ty c y n =
    let* c = var t c in
    let* y = operand t y in
    let+ n = operand t n in
    let n = N (Osel ty, [c; y; n]) in
    let ty = (ty :> ty) in
    let id = new_node ~ty t n in
    let r = Rv.var (regcls ty) x in
    let rid = new_node ~ty t @@ Rv r in
    ignore @@ new_node ~l t @@ N (Omove, [rid; id]);
    setvar t x id;
    setrv t id r

  let call_args_stack_size t l f args =
    C.List.fold args ~init:0 ~f:(fun sz -> function
        | a, o ->
          let* () = C.unless (sz <= o) @@ fun () ->
            C.failf "In Isel_builder.call: call to function %a at label %a \
                     in function $%s has invalid stack offset (%d > %d)"
              Virtual.pp_global f Label.pp l (Func.name t.fn) sz o () in
          typeof_operand t a >>| function
          | #Type.basic as b -> o + (Type.sizeof_basic b / 8)
          | `flag -> o + 1
          | `v128 -> o + 16)
    >>| M.call_args_stack_size

  let call_adj_stack ?(restore = false) t l sz =
    if sz > 0 then begin
      let w = Target.word M.target in
      let rid = new_node ~ty:word t @@ Rv (Rv.reg R.sp) in
      let s = Bv.(int sz mod modulus (Type.sizeof_imm_base w)) in
      let sid = new_node ~ty:word t @@ N (Oint (s, (w :> Type.imm)), []) in
      let op = if restore then `add (w :> Type.basic) else `sub (w :> Type.basic) in
      let id = new_node ~ty:word t @@ N (Obinop op, [rid; sid]) in
      ignore @@ new_node ~l t @@ N (Omove, [rid; id])
    end

  let call_arg_reg t l (a, r) =
    let* ty, a = operand' t a in
    let+ r = reg t r >>| Rv.reg in
    let rid = new_node ~ty t @@ Rv r in
    ignore @@ new_node ~l t @@ N (Omove, [rid; a])

  let call_arg_stk t l (a, o) =
    let+ ty, a = operand' t a in
    let w = Target.word M.target in
    let rid = new_node ~ty:word t @@ Rv (Rv.reg R.sp) in
    let o = Bv.(int o mod modulus (Type.sizeof_imm_base w)) in
    let oid = new_node ~ty:word t @@ N (Oint (o, (w :> Type.imm)), []) in
    let aid = new_node ~ty:word t @@ N (Obinop (`add (w :> Type.basic)), [rid; oid]) in
    let ty = match ty with
      | `flag -> `i8
      | `v128 -> `v128
      | #Type.basic as b -> (b :> [Type.basic | `v128]) in
    ignore @@ new_node ~l t @@ N (Ostore ty, [a; aid])

  let call_ret t l (x, ty, r) =
    let+ r = reg t r in
    let ty = (ty :> ty) in
    let rid = new_node ~ty t @@ Rv (Rv.reg r) in
    let xid = newvar t x ty in
    let n = N (Omove, [xid; rid]) in
    ignore @@ new_node ~l t n

  let call t l ret f args =
    let rargs, sargs, iargs = List.partition3_map args ~f:(function
        | `reg (a, r) ->
          (* Sometimes there are special cases where a register not typically
             used for argument passing needs to be passed (i.e. variadic functions
             in amd64-sysv pass the number of floating point arguments in AL). *)
          if M.Reg.(is_arg @@ of_string_exn r)
          then `Fst (a, r)
          else `Trd (a, r)
        | `stk (a, o) -> `Snd (a, o)) in
    let* sz = call_args_stack_size t l f sargs in
    let* () = C.List.iter rargs ~f:(call_arg_reg t l) in
    call_adj_stack t l sz;
    let* () = C.List.iter sargs ~f:(call_arg_stk t l) in
    let* () = C.List.iter iargs ~f:(call_arg_reg t l) in
    let* f = global t f in
    let callargs =
      List.map (rargs @ iargs) ~f:(fun (_, r) ->
          (* Should be safe to do it here. *)
          Rv.reg @@ M.Reg.of_string_exn r) |>
      List.dedup_and_sort ~compare:Rv.compare in
    let ca = new_node t @@ Callargs callargs in
    ignore @@ new_node ~l t @@ N (Ocall, [ca; f]);
    call_adj_stack t l sz ~restore:true;
    C.List.iter ret ~f:(call_ret t l)

  let load t l x ty a =
    let+ a = operand t a in
    let ty' = (ty :> ty) in
    let n = N (Oload ty, [a]) in
    let lid = new_node ~ty:ty' t n in
    let vid = newvar t x ty' in
    (* TODO: see if we can do a pessimistic alias analysis to forward
       the `Oload` node where this var appears, where possible. *)
    ignore @@ new_node ~l t @@ N (Omove, [vid; lid])

  let store t l ty v a =
    let* v = operand t v in
    let+ a = operand t a in
    let ty' = (ty :> [Type.basic | `v128]) in
    let n = N (Ostore ty', [v; a]) in
    ignore @@ new_node ~l t n

  let regcopy t l x ty r =
    let+ r = reg t r in
    let ty = (ty :> ty) in
    let rid = new_node ~ty t @@ Rv (Rv.reg r) in
    let xid = newvar t x ty in
    let n = N (Omove, [xid; rid]) in
    ignore @@ new_node ~l t n

  let regstore t l r a =
    let* r = reg t r in
    let+ a = operand t a in
    let ty = R.typeof r in
    let rid = new_node ~ty:(ty :> ty) t @@ Rv (Rv.reg r) in
    let n = N (Ostore ty, [rid; a]) in
    ignore @@ new_node ~l t n

  let regassign t l r a =
    let* r = reg t r in
    let* ty = typeof_operand t a in
    let+ a = operand t a in
    let rid = new_node ~ty t @@ Rv (Rv.reg r) in
    let n = N (Omove, [rid; a]) in
    ignore @@ new_node ~l t n

  let stkargs t l x =
    assert t.frame;
    let rid = new_node ~ty:word t @@ Rv (Rv.reg R.fp) in
    let xid = newvar t x word in
    let w = Target.word M.target in
    let off = Bv.(int M.stack_args_offset mod modulus (Type.sizeof_imm_base w)) in
    let oid = new_node ~ty:word t @@ N (Oint (off, (w :> Type.imm)), []) in
    let id = new_node ~ty:word t @@ N (Obinop (`add (w :> Type.basic)), [rid; oid]) in
    !!(ignore @@ new_node ~l t @@ N (Omove, [xid; id]))

  let insn t i =
    let l = Insn.label i in
    match Insn.op i with
    | `bop (x, o, a, b) -> binop t l x o a b
    | `uop (x, o, a) -> unop t l x o a
    | `sel (x, ty, c, y, n) -> sel t l x ty c y n
    | `call (ret, f, args) -> call t l ret f args
    | `load (x, ty, a) -> load t l x ty a
    | `store (ty, v, a) -> store t l ty v a
    | `regcopy (x, ty, r) -> regcopy t l x ty r
    | `regstore (r, a) -> regstore t l r a
    | `regassign (r, a) -> regassign t l r a
    | `stkargs x -> stkargs t l x

  let hlt t l =
    let _id = new_node ~l t @@ N (Ohlt, []) in
    !!()

  let jmp t l d =
    let+ d = dst t l d in
    ignore @@ new_node ~l t @@ N (Ojmp, [d])

  let br t l c y n =
    let* c = var t c in
    let* y = dst ~br:true t l y in
    let+ n = dst ~br:true t l n in
    ignore @@ new_node ~l t @@ N (Obr, [c; y; n])

  let ret t l rets =
    let+ () = C.List.iter rets ~f:(fun (r, a) ->
        let* r = reg t r in
        let+ ty, aid = operand' t a in
        let rid = new_node ~ty t @@ Rv (Rv.reg r) in
        ignore @@ new_node ~l t @@ N (Omove, [rid; aid])) in
    ignore @@ new_node ~l t @@ N (Oret, [])

  let sw t l ty i d tbl =
    let ty' = (ty :> ty) in
    let i = match i with
      | `var x -> newvar t x ty'
      | `sym (s, o) -> new_node ~ty:ty' t @@ N (Osym (s, o), []) in
    let* d, _ = local ~br:true t l d in
    let+ tbl =
      Ctrl.Table.enum tbl |> C.Seq.map ~f:(fun (v, loc) ->
          let+ lbl, _ = local ~br:true t l loc in
          v, lbl) >>| Seq.to_list in
    let tbl' = new_node t @@ Tbl (d, tbl) in
    ignore @@ new_node ~l t @@ N (Osw ty, [i; tbl'])

  let ctrl t l : ctrl -> unit C.t = function
    | `hlt -> hlt t l
    | `jmp d -> jmp t l d
    | `br (c, y, n) -> br t l c y n
    | `ret rets -> ret t l rets
    | `sw (ty, i, d, tbl) -> sw t l ty i d tbl

  let regparam t l (x, r, ty) =
    let+ r = reg t r in
    let ty = (ty :> ty) in
    let rid = new_node ~ty t @@ Rv (Rv.reg r) in
    let xid = newvar t x ty in
    ignore @@ new_node ~l t @@ N (Omove, [xid; rid])

  let stkparam t l (x, o, ty) =
    let ty' = (ty :> ty) in
    let w = Target.word M.target in
    let wi = (w :> Type.imm) in
    let wb = (w :> Type.basic) in
    let xid = newvar t x ty' in
    (* Use the frame pointer. It will make our lives much easier. *)
    let rid = new_node ~ty:word t @@ Rv (Rv.reg R.fp) in
    let o' = o + M.stack_args_offset in
    let o = Bv.(int o' mod modulus (Type.sizeof_imm_base w)) in
    let oid = new_node ~ty:word t @@ N (Oint (o, wi), []) in
    let aid = new_node ~ty:word t @@ N (Obinop (`add wb), [rid; oid]) in
    let lid = new_node ~ty:word t @@ N (Oload ty, [aid]) in
    ignore @@ new_node ~l t @@ N (Omove, [xid; lid]);
    !!()

  (* TODO: stack stuff

     I think would suffice to just make the binding to the variable available
     and then maintain the slot abstraction up to register allocation, because
     at that point we will have more information on how to lay out the stack.
  *)
  let slot t _l s =
    let _sid = newvar t (Slot.var s) word in
    ()

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
      Semi_nca.Tree.children t.dom l |>
      Seq.to_list |> List.sort ~compare:cmp |>
      List.iter ~f:(Stack.push q)
    with Missing_rpo l ->
      C.failf "In Isel_builder.enqueue: missing RPO number for label %a in function $%s"
        Label.pp l (Func.name t.fn) ()

  let initial t =
    let entry = Func.entry t.fn in
    let b = Label.Tree.find_exn t.blks entry in
    let l = match Seq.hd @@ Blk.insns b with
      | Some i -> Insn.label i
      | None -> entry in
    let rargs, sargs =
      Func.args t.fn |> Seq.to_list |>
      List.partition_map ~f:(fun (a, ty) -> match a with
          | `reg (x, r) -> First (x, r, ty)
          | `stk (x, o) -> Second (x, o, ty)) in
    let* () = C.List.iter sargs ~f:(stkparam t l) in
    let+ () = C.List.iter rargs ~f:(regparam t l) in
    Func.slots t.fn |> Seq.iter ~f:(fun s -> slot t l s)

  let run t =
    let rec loop q = match Stack.pop q with
      | None -> !!()
      | Some l ->
        let* () = step t l in
        let* () = enqueue t l q in
        loop q in
    let* () = initial t in
    loop @@ Stack.singleton Label.pseudoentry
end
