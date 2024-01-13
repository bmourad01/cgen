open Core
open Virtual
open Sysv_common

open Context.Syntax

(* A compound argument to a call passed in a single register. *)
let onereg_arg ~reg k r src =
  let t = reg_type r in
  let* l, li = Cv.Abi.load t (`var src) in
  let+ callai, callar, callam = match reg r with
    | Some r ->
      let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy t, `var l) in
      k.callai @>* [li; i],
      k.callar @> r,
      k.callam
    | None ->
      !!(k.callai @> li,
         k.callar,
         k.callam @> `var l) in
  {k with callai; callar; callam}

(* A compound argument to a call passed in two registers. *)
let tworeg_arg ~reg2 k r1 r2 src =
  let t1 = reg_type r1 and t2 = reg_type r2 in
  let regs = reg2 r1 r2 in
  let* o, oi = Cv.Abi.binop (`add `i64) (`var src) (i64 8) in
  let* l1, li1 = Cv.Abi.load `i64 (`var src) in
  let* l2, li2 = Cv.Abi.load `i64 (`var o) in
  let+ callai, callar, callam = match regs with
    | Some (r1, r2) ->
      let* i1 = Cv.Abi.insn @@ `uop (`reg r1, `copy t1, `var l1) in
      let+ i2 = Cv.Abi.insn @@ `uop (`reg r2, `copy t2, `var l2) in
      k.callai @>* [li1; oi; li2; i1; i2],
      k.callar @>* [r1; r2],
      k.callam
    | None ->
      !!(k.callai @>* [li1; oi; li2],
         k.callar,
         k.callam @>* [`var l1; `var l2]) in
  {k with callai; callar; callam}

(* A compound argument to a call passed in memory. *)
let memory_arg k size src =
  if size > 0 then
    let+ ldm = Cv.Abi.ldm `i64 src size in
    let callai, callam =
      List.fold ldm ~init:(k.callai, k.callam) ~f:(fun (ai, am) i ->
          let am = match Abi.Insn.op i with
            | `load (x, _, _) -> am @> (x :> Abi.operand)
            | _ -> am in
          ai @> i, am) in
    {k with callai; callam}
  else
    (* Technically we're not passing the contents, but since it's
       empty the contents are junk anyway. This only needs to be
       here for alignment. *)
    !!{k with callam = k.callam @> (src :> Abi.operand)}

let call_ret_basic x t k =
  let r, t = match (t : Type.ret) with
    | #Type.fp as f -> sse_rets.(0), f
    | #Type.imm as m -> int_rets.(0), m
    | `si8 -> int_rets.(0), `i8
    | `si16 -> int_rets.(0), `i16
    | `si32 -> int_rets.(0), `i32
    | `name _ -> assert false in
  let+ i = Cv.Abi.insn @@ `uop (`var x, `copy t, `reg r) in
  {k with callri = k.callri @> i; callrr = [r]}

(* Fits in one register. *)
let call_ret_onereg env x r k =
  let x = find_ref env x in
  let t = reg_type r in
  let reg = match t with
    | `i64 -> int_rets.(0)
    | `f64 -> sse_rets.(0) in
  let+ st = Cv.Abi.store t (`reg reg) (`var x) in
  {k with callri = k.callri @> st; callrr = [reg]}

(* Fits in two registers. *)
let call_ret_tworeg env x r1 r2 k =
  let x = find_ref env x in
  let t1 = reg_type r1 and t2 = reg_type r2 in
  let reg1, reg2 = match t1, t2 with
    | `i64, `i64 -> int_rets.(0), int_rets.(1)
    | `i64, `f64 -> int_rets.(0), sse_rets.(0)
    | `f64, `i64 -> sse_rets.(0), int_rets.(0)
    | `f64, `f64 -> sse_rets.(0), sse_rets.(1) in
  let* o, oi = Cv.Abi.binop (`add `i64) (`var x) (i64 8) in
  let* st1 = Cv.Abi.store t1 (`reg reg1) (`var x) in
  let+ st2 = Cv.Abi.store t2 (`reg reg2) (`var o) in
  let callri = k.callri @>* [oi; st1; st2] in
  {k with callri; callrr = [reg1; reg2]}

(* Passed as a reference to memory. We need to allocate
   a new stack slot for this one. *)
let call_ret_memory env x lk k =
  let r = int_args.(0) in
  let* y = new_slot env lk.size lk.align in
  let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy `i64, `var y) in
  let callai = k.callai @> i in
  let callar = r <@ k.callar in
  Hashtbl.set env.refs ~key:x ~data:y;
  {k with callai; callar; callrr = [int_rets.(0)]}

(* Handle the compound type return value of a call.  *)
let lower_call_ret env kret k = match kret with
  | `none -> !!k
  | `basic (x, t) -> call_ret_basic x t k
  | `compound (x, lk) -> match lk.cls with
    | Kreg _ when lk.size = 0 -> assert false
    | Kreg (r, _) when lk.size = 8 -> call_ret_onereg env x r k
    | Kreg (r1, r2) -> call_ret_tworeg env x r1 r2 k
    | Kmem when lk.size = 0 -> !!k
    | Kmem -> call_ret_memory env x lk k

let expect_arg_var env l : operand -> Var.t Context.t = function
  | `var x -> !!x
  | x ->
    Context.failf
      "Expected var for `call` operand in block %a \
       of function $%s, got %a" Label.pp l
      (Func.name env.fn) pp_operand x ()

(* Figure out how we should pass the argument `a` at the call site. *)
let classify_call_arg ~reg ~reg2 env key k a =
  typeof_operand env a >>= function
  | #Type.imm as m ->
    (* Use an integer register. *)
    begin match reg Rint with
      | None -> !!{k with callam = k.callam @> oper a}
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy m, oper a) in
        let callai = k.callai @> i in
        let callar = k.callar @> r in
        {k with callai; callar}
    end
  | #Type.fp as f ->
    (* Use an SSE register. *)
    begin match reg Rsse with
      | None -> !!{k with callam = k.callam @> oper a}
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy f, oper a) in
        let callai = k.callai @> i in
        let callar = k.callar @> r in
        {k with callai; callar}
    end
  | `flag -> assert false
  | `compound (s, _, _) | `opaque (s, _, _) ->
    (* Figure out what class this type is. *)
    let* lk = type_cls env s in
    let* x = expect_arg_var env key a in
    let src = find_ref env x in
    match lk.cls with
    | Kreg _ when lk.size = 0 -> assert false
    | Kreg (r, _) when lk.size = 8 -> onereg_arg ~reg k r src
    | Kreg (r1, r2) -> tworeg_arg ~reg2 k r1 r2 src
    | Kmem -> memory_arg k lk.size (`var src)

(* See `Sysv_params.alloc_onereg`. *)
let alloc_onereg ~qi ~qs = function
  | Rint -> Stack.pop qi
  | Rsse -> Stack.pop qs
  | Rnone -> assert false

(* See `Sysv_params.alloc_tworeg`. *)
let alloc_tworeg ~qi ~qs r1 r2 = match r1, r2 with
  | Rint, Rint ->
    if Stack.length qi >= 2 then
      let r1 = Stack.pop_exn qi in
      let r2 = Stack.pop_exn qi in
      Some (r1, r2)
    else None
  | Rsse, Rsse ->
    if Stack.length qs >= 2 then
      let r1 = Stack.pop_exn qs in
      let r2 = Stack.pop_exn qs in
      Some (r1, r2)
    else None
  | Rint, Rsse ->
    if Stack.length qi >= 1
    && Stack.length qs >= 1 then
      let r1 = Stack.pop_exn qi in
      let r2 = Stack.pop_exn qs in
      Some (r1, r2)
    else None
  | Rsse, Rint ->
    if Stack.length qs >= 1
    && Stack.length qi >= 1 then
      let r1 = Stack.pop_exn qs in
      let r2 = Stack.pop_exn qi in
      Some (r1, r2)
    else None
  | Rnone, _ | _, Rnone -> assert false

(* Lower the `call` instructions. *)
let lower env = iter_blks env ~f:(fun b ->
    Blk.insns b |> Context.Seq.iter ~f:(fun i ->
        match Insn.op i with
        | `call (ret, _, args, vargs) ->
          let key = Insn.label i in
          let qi = int_arg_queue () in
          let qs = sse_arg_queue () in
          let reg = alloc_onereg ~qi ~qs in
          let reg2 = alloc_tworeg ~qi ~qs in
          (* See if we're returning a compound type. *)
          let* kret = match ret with
            | Some (x, `name n) ->
              (* Check for implicit first parameter. *)
              let* lk = type_cls env n in
              begin match lk.cls with
                | Kmem when lk.size > 0 -> ignore (Stack.pop_exn qi)
                | _ -> ()
              end;
              !!(`compound (x, lk))
            | Some (x, t) -> !!(`basic (x, t))
            | None -> !!`none in
          (* Process each argument. *)
          let acls = classify_call_arg ~reg ~reg2 env key in
          let* k = Context.List.fold args ~init:empty_call ~f:acls in
          let* k = Context.List.fold vargs ~init:k ~f:acls in
          (* If this is a variadic call, then RAX must hold the number
             of SSE registers that were used to pass parameters. *)
          let* k = match vargs with
            | [] -> !!k
            | _ ->
              let n = num_sse_args - Stack.length qs in
              let+ i = Cv.Abi.insn @@ `uop (`reg "rax", `copy `i8, i8 n) in
              {k with callai = k.callai @> i} in
          (* Process the return value. *)
          let+ k = lower_call_ret env kret k in
          Hashtbl.set env.calls ~key ~data:k
        | _ -> !!()))

