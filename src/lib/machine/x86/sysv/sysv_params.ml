open Core
open Regular.Std
open Virtual
open Sysv_common

(* pre: `al` is a power of 2

   Note that for all basic types, `sz` and `al` are 8.
*)
let onext ofs sz al =
  let o = (!ofs + al - 1) land -al in
  ofs := o + sz;
  o

let basic_param ~ofs ~reg env t x =
  let pvar = match reg t with
    | Some r -> `reg (x, r)
    | None ->
      let o = onext ofs 8 8 in
      `stk (x, o) in
  Vec.push env.params @@ {pty = t; pvar; pins = []}

(* Allocate a single register as a parameter or
   pass it on the stack. *)
let alloc_onereg ~qi ~qs = function
  | #Type.imm -> Stack.pop qi
  | #Type.fp -> Stack.pop qs

(* Allocate two registers as a parameter. Both
   must be available, or the argument is passed
   on the stack. *)
let alloc_tworeg ~qi ~qs t1 t2 = match t1, t2 with
  | #Type.imm, #Type.imm ->
    if Stack.length qi >= 2 then
      let r1 = Stack.pop_exn qi in
      let r2 = Stack.pop_exn qi in
      Some (r1, r2)
    else None
  | #Type.fp, #Type.fp ->
    if Stack.length qs >= 2 then
      let r1 = Stack.pop_exn qs in
      let r2 = Stack.pop_exn qs in
      Some (r1, r2)
    else None
  | #Type.imm, #Type.fp ->
    if Stack.length qi >= 1
    && Stack.length qs >= 1 then
      let r1 = Stack.pop_exn qi in
      let r2 = Stack.pop_exn qs in
      Some (r1, r2)
    else None
  | #Type.fp, #Type.imm ->
    if Stack.length qs >= 1
    && Stack.length qi >= 1 then
      let r1 = Stack.pop_exn qs in
      let r2 = Stack.pop_exn qi in
      Some (r1, r2)
    else None

module Make(Context : Context_intf.S_virtual) = struct
  open Context.Syntax
  open Make0(Context)
  module Cv = Context.Virtual

  let init_regs env =
    let qi = int_arg_queue () in
    let qs = sse_arg_queue () in
    let+ () = match Func.return env.fn with
      | Some (#Type.basic | `si8 | `si16 | `si32) | None -> !!()
      | Some `name n -> type_cls env n >>= function
        | {cls = Kmem; size; _} when size > 0 ->
          (* Return value is blitted to a memory address, which is
             implicity passed as the first integer register. *)
          let r = Stack.pop_exn qi in
          let+ x = Context.Var.fresh in
          let p = {pty = `i64; pvar = `reg (x, r); pins = []} in
          Vec.push env.params p;
          env.rmem <- Some x
        | _ -> !!() in
    alloc_onereg ~qi ~qs,
    alloc_tworeg ~qi ~qs

  (* Pass in a single register, so we can reuse `x`. *)
  let onereg_param ~ofs ~reg env x y r =
    let t = reg_type r in
    let+ pvar, pins = match reg t with
      | None ->
        let o = onext ofs 8 8 in
        let+ st = Cv.Abi.store t (`var x) (`var y) in
        `stk (x, o), [st]
      | Some r ->
        let+ st = Cv.Abi.store t (`var x) (`var y) in
        `reg (x, r), [st] in
    Vec.push env.params @@ {pty = t; pvar; pins}

  (* Insert fresh parameters for the two-reg argument. *)
  let tworeg_param ~ofs ~reg2 env y r1 r2 =
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let* x1 = Context.Var.fresh in
    let* x2 = Context.Var.fresh in
    let* o, oi = Cv.Abi.binop (`add `i64) (`var y) (i64 8) in
    let* st1 = Cv.Abi.store t1 (`var x1) (`var y) in
    let+ st2 = Cv.Abi.store t1 (`var x2) (`var o) in
    let p1, p2 = match reg2 t1 t2 with
      | None ->
        let o1 = onext ofs 8 8 in
        let o2 = onext ofs 8 8 in
        let p1 = {pty = t1; pvar = `stk (x1, o1); pins = [st1]} in
        let p2 = {pty = t2; pvar = `stk (x2, o2); pins = [oi; st2]} in
        p1, p2
      | Some (r1, r2) ->
        let p1 = {pty = t1; pvar = `reg (x1, r1); pins = [st1]} in
        let p2 = {pty = t2; pvar = `reg (x2, r2); pins = [oi; st2]} in
        p1, p2 in
    Vec.push env.params p1;
    Vec.push env.params p2

  (* Blit the structure to a stack slot. *)
  let memory_param ~ofs env y size align =
    let so = onext ofs size align in
    let size' = if size = 0 then align else size in
    Seq.init (size' / 8) ~f:(fun i -> i * 8) |>
    Context.Seq.iter ~f:(fun o ->
        let* x = Context.Var.fresh in
        let+ pins =
          if size = 0 then
            (* The empty structure contains garbage. *)
            !![]
          else if o = 0 then
            let+ st = Cv.Abi.store `i64 (`var x) (`var y) in
            [st]
          else
            let* o, oi = Cv.Abi.binop (`add `i64) (`var y) (i64 o) in
            let+ st = Cv.Abi.store `i64 (`var x) (`var o) in
            [oi; st] in
        let p = {pty = `i64; pvar = `stk (x, so + o); pins} in
        Vec.push env.params p)

  (* Quoting from the System V document, section 3.5.7:

     "The prologue of a function taking a variable argument list
      and known to call the macro va_start is expected to save the
      argument registers to the register save area."
  *)
  let needs_register_save env =
    Func.variadic env.fn &&
    Func.blks env.fn |>
    Seq.exists ~f:(fun b ->
        Blk.insns b |>
        Seq.map ~f:Insn.op |>
        Seq.exists ~f:(function
            | `vastart _ -> true
            | _ -> false))

  let register_save_int env params sse s =
    let* label = Context.Label.fresh in
    let* save =
      Array.to_sequence_mutable int_args |>
      Seq.mapi ~f:(fun i r -> i * 8, r) |>
      Seq.filter ~f:(fun (_, r) -> not @@ Set.mem params r) |>
      Context.Seq.fold ~init:Ftree.empty ~f:(fun acc -> function
          | 0, r ->
            let+ st = Cv.Abi.regstore r (`var s) in
            acc @> st
          | o, r ->
            let* o, oi = Cv.Abi.binop (`add `i64) (`var s) (i64 o) in
            let+ st = Cv.Abi.regstore r (`var o) in
            acc @>* [oi; st]) in
    let zero = `int (Bv.zero, `i8) in
    assert (Option.is_none env.alpar);
    let* r =  Context.Var.fresh in
    env.alpar <- Some r;
    let+ z, zi = Cv.Abi.binop (`eq `i8) (`var r) zero in
    let entry = `label (Func.entry env.fn, []) in
    let sse = `label (sse, []) in
    Abi.Blk.create () ~label
      ~insns:(Ftree.to_list (save @> zi))
      ~ctrl:(`br (z, entry, sse))

  let rsave_sse_ofs = 48

  let register_save_sse env params label s =
    let+ save =
      Array.to_sequence_mutable sse_args |>
      Seq.mapi ~f:(fun i r -> i64 (i * 16 + rsave_sse_ofs), r) |>
      Seq.filter ~f:(fun (_, r) -> not @@ Set.mem params r) |>
      Context.Seq.fold ~init:Ftree.empty ~f:(fun acc (o, r) ->
          let* o, oi = Cv.Abi.binop (`add `i64) (`var s) o in
          let+ st = Cv.Abi.regstore r (`var o) in
          acc @>* [oi; st]) in
    let entry = `label (Func.entry env.fn, []) in
    Abi.Blk.create () ~label
      ~insns:(Ftree.to_list save)
      ~ctrl:(`jmp entry)

  let compute_register_save_area env =
    Context.when_ (needs_register_save env) @@ fun () ->
    let params = Vec.fold env.params ~init:String.Set.empty
        ~f:(fun acc p -> match p.pvar with
            | `reg (_, r) -> Set.add acc r
            | `stk _ -> acc) in
    let* rsslot = new_slot env 176 16 in
    let* sse = Context.Label.fresh in
    let* rsint = register_save_int env params sse rsslot in
    let+ rssse = register_save_sse env params sse rsslot in
    env.rsave <- Some {rsslot; rsint; rssse}

  (* Lower the parameters of the function and copy their contents
     to SSA variables or stack slots. *)
  let lower_params env =
    let ofs = ref 0 in
    let* reg, reg2 = init_regs env in
    Func.args env.fn |>
    Context.Seq.iter ~f:(fun (x, t) -> match t with
        | #Type.basic as t ->
          !!(basic_param ~ofs ~reg env t x)
        | `name s ->
          let* k = type_cls env s in
          let* y = if k.size > 0
            then new_slot env k.size k.align
            else !!x in
          Hashtbl.set env.refs ~key:x ~data:y;
          match k.cls with
          | Kreg _ when k.size = 0 -> assert false
          | Kreg (r, _) when k.size = 8 -> onereg_param ~ofs ~reg env x y r
          | Kreg (r1, r2) -> tworeg_param ~ofs ~reg2 env y r1 r2
          | Kmem -> memory_param ~ofs env y k.size k.align)

  let lower env =
    let* () = lower_params env in
    compute_register_save_area env
end
