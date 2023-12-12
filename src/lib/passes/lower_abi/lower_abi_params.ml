open Core
open Regular.Std
open Virtual
open Lower_abi_common

open Context.Syntax

(* Allocate a single register as a parameter or
   pass it on the stack. *)
let alloc_onereg qi qs = function
  | #Type.imm -> Stack.pop qi
  | #Type.fp -> Stack.pop qs

(* Allocate two registers as a parameter. Both
   must be available, or the argument is passed
   on the stack. *)
let alloc_tworeg qi qs t1 t2 = match t1, t2 with
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

let init_regs env =
  let qi = int_arg_queue () in
  let qs = sse_arg_queue () in
  let+ () = match Func.return env.fn with
    | Some (#Type.basic | `si8 | `si16 | `si32) | None -> !!()
    | Some `name n -> type_cls env n >>= function
      | {cls = Kmem; _} ->
        let r = int_args.(0) in
        let* x = Context.Var.fresh in
        let+ i = Cv.Abi.insn @@ `uop (`var x, `copy `i64, `reg r) in
        let p = {pty = `i64; pvar = `reg r; pins = [i]} in
        Vec.push env.params p;
        env.rmem <- Some x;
        ignore (Stack.pop_exn qi)
      | _ -> !!() in
  alloc_onereg qi qs,
  alloc_tworeg qi qs

let basic_param ~reg env t x =
  let+ pvar, pins = match reg t with
    | None -> !!(`var x, [])
    | Some r ->
      let+ i = Cv.Abi.insn @@ `uop (`var x, `copy t, `reg r) in
      `reg r, [i] in
  Vec.push env.params @@ {pty = t; pvar; pins}

(* Pass in a single register, so we can reuse `x`. *)
let onereg_param ~reg env x y r =
  let t = reg_type r in
  let+ pvar, pins = match reg t with
    | None ->
      let+ st = Cv.Abi.store t (`var x) (`var y) in
      `var x, [st]
    | Some r ->
      let* i = Cv.Abi.insn @@ `uop (`var x, `copy t, `reg r) in
      let+ st = Cv.Abi.store t (`var x) (`var y) in
      `reg r, [i; st] in
  Vec.push env.params @@ {pty = t; pvar; pins}

(* Insert fresh parameters for the two-reg argument. *)
let tworeg_param ~reg2 env y r1 r2 =
  let t1 = reg_type r1 and t2 = reg_type r2 in
  let* x1 = Context.Var.fresh in
  let* x2 = Context.Var.fresh in
  let* o, oi = Cv.Abi.binop (`add `i64) (`var y) o8 in
  let* st1 = Cv.Abi.store t1 (`var x1) (`var y) in
  let* st2 = Cv.Abi.store t1 (`var x2) (`var o) in
  let+ p1, p2 = match reg2 t1 t2 with
    | None ->
      let p1 = {pty = t1; pvar = `var x1; pins = [st1]} in
      let p2 = {pty = t2; pvar = `var x2; pins = [oi; st2]} in
      !!(p1, p2)
    | Some (r1, r2) ->
      let* i1 = Cv.Abi.insn @@ `uop (`var x1, `copy t1, `reg r1) in
      let+ i2 = Cv.Abi.insn @@ `uop (`var x2, `copy t2, `reg r2) in
      let p1 = {pty = t1; pvar = `reg r1; pins = [i1; st1]} in
      let p2 = {pty = t2; pvar = `reg r2; pins = [i2; oi; st2]} in
      p1, p2 in
  Vec.push env.params p1;
  Vec.push env.params p2

(* Blit the structure to a stack slot. *)
let memory_param env y size =
  Seq.init (size / 8) ~f:(fun i -> i * 8) |>
  Context.Seq.iter ~f:(fun o ->
      let* x = Context.Var.fresh in
      let+ pins =
        if o = 0 then
          let+ st = Cv.Abi.store `i64 (`var x) (`var y) in
          [st]
        else
          let* o, oi = Cv.Abi.binop (`add `i64) (`var y) (i64 o) in
          let+ st = Cv.Abi.store `i64 (`var x) (`var o) in
          [oi; st] in
      let p = {pty = `i64; pvar = `var x; pins} in
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

let register_save_int env sse s =
  let* label = Context.Label.fresh in
  let* save =
    Array.to_list int_args |>
    List.mapi ~f:(fun i r -> i * 8, r) |>
    Context.List.map ~f:(fun (o, r) ->
        if o = 0 then
          let+ st = Cv.Abi.store `i64 (`reg r) (`var s) in
          [st]
        else
          let* o, oi = Cv.Abi.binop (`add `i64) (`var s) (i64 o) in
          let+ st = Cv.Abi.store `i64 (`reg r) (`var o) in
          [oi; st]) in
  let zero = `int (Bv.zero, `i8) in
  let+ z, zi = Cv.Abi.binop (`eq `i8) (`reg "RAX") zero in
  let entry = `label (Func.entry env.fn, []) in
  let sse = `label (sse, []) in
  Abi.Blk.create () ~label
    ~insns:(List.concat save @ [zi])
    ~ctrl:(`br (`var z, entry, sse))

let register_save_sse env label s =
  let+ save =
    Array.to_list sse_args |>
    List.mapi ~f:(fun i r -> i64 (i * 16 + rsave_sse_ofs), r) |>
    Context.List.map ~f:(fun (o, r) ->
        let* o, oi = Cv.Abi.binop (`add `i64) (`var s) o in
        let+ st = Cv.Abi.storev r (`var o) in
        [oi; st]) in
  let entry = `label (Func.entry env.fn, []) in
  Abi.Blk.create () ~label ~insns:(List.concat save) ~ctrl:(`jmp entry)

let compute_register_save_area env =
  if needs_register_save env then
    let* rsslot = new_slot env 176 16 in
    let* sse = Context.Label.fresh in
    let* rsint = register_save_int env sse rsslot in
    let+ rssse = register_save_sse env sse rsslot in
    env.rsave <- Some {rsslot; rsint; rssse}
  else !!()

(* Lower the parameters of the function and copy their contents
   to SSA variables or stack slots. *)
let lower env =
  let* reg, reg2 = init_regs env in
  let* () =
    Func.args env.fn |>
    Context.Seq.iter ~f:(fun (x, t) -> match t with
        | #Type.basic as t -> basic_param ~reg env t x
        | `name s ->
          let* k = type_cls env s in
          let* y = new_slot env k.size k.align in
          Hashtbl.set env.refs ~key:x ~data:y;
          match k.cls with
          | Kreg _ when k.size = 0 -> !!()
          | Kreg (r, _) when k.size = 8 -> onereg_param ~reg env x y r
          | Kreg (r1, r2) -> tworeg_param ~reg2 env y r1 r2
          | Kmem -> memory_param env y k.size) in
  compute_register_save_area env
