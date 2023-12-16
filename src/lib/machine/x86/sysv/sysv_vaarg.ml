(* Rough sketch of the logic behind `vaarg` for a given type `t`:

   @bcmp:
     %a = add.l %ap, ofs     ; Load gp or fp offset.
     %o = ld.w %a            ;
     %c = le.w %o, limit-inc ; Check to see if we've exhausted the
     br %c, @breg, @bstk     ; register save area.
   @breg:
     %a = add.l %ap, 16      ; Load `reg_save_area`.
     %l = ld.l %a            ;
     %r = add.l %l, %o       ; Pointer to the next register.
     %n = add.w %o, inc      ; Increment the offset.
     %a = add.l %ap, ofs     ; Update the offset in %ap.
     st.w %n, %a             ;
     jmp @bjoin(%r)
   @bstk:
     %a = add.l %ap, 8       ; Load `overflow_arg_area`; this is
     %l = ld.l %a            ; the next arg on the stack.
     %n = add.l %l, sinc     ; Increment the pointer.
     st.l %n, %a             ; Update the pointer.
     jmp @bjoin(%l)
   @bjoin(%p):
     %x = ld.t %p            ; Return the fetched type.
     jmp @cont               ; Resume execution.
*)

open Core
open Virtual
open Sysv_common

open Context.Syntax

(* Check if we've reached the limit for `{gp,fp}_offset`. *)
let make_cmp ?(num = 1) label t ap yes no =
  (* Fetch the offset into the register save area. *)
  let* o, a, oi, limit, inc = match t with
    | #Type.imm ->
      let+ o, oi = Cv.Abi.load `i32 ap in
      o, ap, [oi], 48, 8 * num
    | #Type.fp ->
      let* a, ai = Cv.Abi.binop (`add `i64) ap o4 in
      let+ o, oi = Cv.Abi.load `i32 (`var a) in
      o, `var a, [ai; oi], 176, 16 * num in
  (* Check if there is enough room. *)
  let+ c, ci = Cv.Abi.binop (`le `i32) (`var o) (i32 (limit - inc)) in
  let locyes = `label (yes, []) in
  let locno = `label (no, []) in
  let b = Abi.Blk.create () ~label
      ~insns:(oi @ [ci])
      ~ctrl:(`br (`var c, locyes, locno)) in
  b, o, a, inc

(* Fetch `num` registers of type `t`. *)
let fetch_reg ?(num = 1) env x t ap cont =
  let* lcmp = Context.Label.fresh in
  let* lreg = Context.Label.fresh in
  let* lstk = Context.Label.fresh in
  let* ljoin = Context.Label.fresh in
  let* bcmp, o, a1, inc = make_cmp ~num lcmp t ap lreg lstk in
  (* Access the register save area and increment the reg
     offset. *)
  let* a, ai = Cv.Abi.binop (`add `i64) ap o16 in
  let* l, li = Cv.Abi.load `i64 (`var a) in
  let* r, ri = Cv.Abi.binop (`add `i64) (`var l) (`var o) in
  let* n, ni = Cv.Abi.binop (`add `i32) (`var o) (i32 inc) in
  let* st = Cv.Abi.store `i32 (`var n) a1 in
  let breg =
    Abi.Blk.create ()
      ~label:lreg
      ~insns:[ai; li; ri; ni; st]
      ~ctrl:(`jmp (`label (ljoin, [`var r]))) in
  (* Access the overflow arg area and increment it. *)
  let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
  let* l, li = Cv.Abi.load `i64 (`var a) in
  let* n, ni = Cv.Abi.binop (`add `i64) (`var l) (i64 (num * 8)) in
  let* st = Cv.Abi.store `i64 (`var n) (`var a) in
  let bstk =
    Abi.Blk.create ()
      ~label:lstk
      ~insns:[ai; li; ni; st]
      ~ctrl:(`jmp (`label (ljoin, [`var l]))) in
  (* Join the results. *)
  let* p = Context.Var.fresh in
  (* Check if this is a struct; if so we need to blit it
     to the appropriate stack slot. *)
  let* res = match Hashtbl.find env.refs x with
    | Some y -> Cv.Abi.blit `i64 (8 * num) ~src:(`var p) ~dst:(`var y)
    | None ->
      let+ li = Cv.Abi.insn @@ `load (`var x, t, `var p) in
      [li] in
  let bjoin =
    Abi.Blk.create ()
      ~label:ljoin
      ~args:[p]
      ~insns:res
      ~ctrl:(`jmp (`label (cont, []))) in
  !![bcmp; breg; bstk; bjoin]

let check_different t1 t2 = match t1, t2 with
  | `i64, `f64 | `f64, `i64 -> true
  | `i64, `i64 -> false
  | `f64, `f64 -> false

(* Fetch two register classes at once, assuming that they are
   different. *)
let fetch_two_reg env x t1 t2 ap cont =
  assert (check_different t1 t2);
  let* lcmp1 = Context.Label.fresh in
  let* lcmp2 = Context.Label.fresh in
  let* lreg = Context.Label.fresh in
  let* lstk = Context.Label.fresh in
  let* ljoin = Context.Label.fresh in
  (* Check if both registers can be fetched from the register
     save area. *)
  let* bcmp1, o1, a1, inc1 = make_cmp lcmp1 t1 ap lcmp2 lstk in
  let* bcmp2, o2, a2, inc2 = make_cmp lcmp2 t2 ap lreg lstk in
  (* Access the register save area and increment. *)
  let* a, ai = Cv.Abi.binop (`add `i64) ap o16 in
  let* l, li = Cv.Abi.load `i64 (`var a) in
  let* r1, ri1 = Cv.Abi.binop (`add `i64) (`var l) (`var o1) in
  let* r2, ri2 = Cv.Abi.binop (`add `i64) (`var l) (`var o2) in
  let* n1, ni1 = Cv.Abi.binop (`add `i32) (`var o1) (i64 inc1) in
  let* n2, ni2 = Cv.Abi.binop (`add `i32) (`var o2) (i64 inc2) in
  let* st1 = Cv.Abi.store `i32 (`var n1) a1 in
  let* st2 = Cv.Abi.store `i32 (`var n2) a2 in
  let breg =
    Abi.Blk.create ()
      ~label:lreg
      ~insns:[ai; li; ri1; ri2; ni1; ni2; st1; st2]
      ~ctrl:(`jmp (`label (ljoin, [`var r1; `var r2]))) in
  (* Access the overflow arg area and increment *)
  let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
  let* l1, li1 = Cv.Abi.load `i64 (`var a) in
  let* l2, li2 = Cv.Abi.binop (`add `i64) (`var l1) o8 in
  let* n, ni = Cv.Abi.binop (`add `i64) (`var l1) o16 in
  let* st = Cv.Abi.store `i64 (`var n) (`var a) in
  let bstk =
    Abi.Blk.create ()
      ~label:lstk
      ~insns:[ai; li1; li2; ni; st]
      ~ctrl:(`jmp (`label (ljoin, [`var l1; `var l2]))) in
  (* Join the results. *)
  let* p1 = Context.Var.fresh in
  let* p2 = Context.Var.fresh in
  let y = find_ref env x in
  let* l, li1 = Cv.Abi.load `i64 (`var p1) in
  let* st1 = Cv.Abi.store `i64 (`var l) (`var y) in
  let* l, li2 = Cv.Abi.load `i64 (`var p2) in
  let* a, ai = Cv.Abi.binop (`add `i64) (`var y) o8 in
  let+ st2 = Cv.Abi.store `i64 (`var l) (`var a) in
  let bjoin =
    Abi.Blk.create ()
      ~label:ljoin
      ~args:[p1; p2]
      ~insns:[li1; st1; li2; ai; st2]
      ~ctrl:(`jmp (`label (cont, []))) in
  [bcmp1; bcmp2; breg; bstk; bjoin]

let fetch env x t ap cont = match (t : Type.arg) with
  | #Type.imm as m -> fetch_reg env x m ap cont
  | #Type.fp as f -> fetch_reg env x f ap cont
  | `name s ->
    let* k = type_cls env s in
    match k.cls with
    | Kreg _ when k.size = 0 ->
      (* Should be handled by `check_empty`. *)
      assert false
    | Kreg (r, _) when k.size = 8 ->
      assert (Hashtbl.mem env.refs x);
      begin match reg_type r with
        | `i64 -> fetch_reg env x `i64 ap cont
        | `f64 -> fetch_reg env x `f64 ap cont
      end
    | Kreg (r1, r2) ->
      assert (Hashtbl.mem env.refs x);
      begin match reg_type r1, reg_type r2 with
        | `i64, `i64 -> fetch_reg ~num:2 env x `i64 ap cont
        | `f64, `f64 -> fetch_reg ~num:2 env x `f64 ap cont
        | t1, t2 -> fetch_two_reg env x t1 t2 ap cont
      end
    | Kmem ->
      (* The struct is passed in memory, so we simply blit from
         the `overflow_arg_area` to the corresponding stack slot. *)
      let y = find_ref env x in
      let* label = Context.Label.fresh in
      let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
      let* l, li = Cv.Abi.load `i64 (`var a) in
      let* n, ni = Cv.Abi.binop (`add `i64) (`var l) (i64 k.size) in
      let* st = Cv.Abi.store `i64 (`var n) (`var a) in
      let+ blit = Cv.Abi.blit `i64 k.size
          ~src:(`var l) ~dst:(`var y) in
      List.return @@ Abi.Blk.create () ~label
        ~insns:([ai; li; ni; st] @ blit)
        ~ctrl:(`jmp (`label (cont, [])))

let check_empty env = function
  | #Type.basic -> !!false
  | `name s ->
    let+ k = type_cls env s in
    k.size = 0

let lower env = iter_blks env ~f:(fun b ->
    Blk.insns b |> Context.Seq.iter ~f:(fun i ->
        match Insn.op i with
        | `vaarg (x, t, ap) ->
          begin check_empty env t >>= function
            | true -> !!()
            | false ->
              let ap = Sysv_vastart.ap_oper ap in
              let* vacont = Context.Label.fresh in
              let+ vablks = fetch env x t ap vacont in
              Hashtbl.set env.vaarg
                ~key:(Insn.label i)
                ~data:{vablks; vacont}
          end
        | _ -> !!()))
