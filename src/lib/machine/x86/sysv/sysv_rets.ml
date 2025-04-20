open Core
open Virtual
open Sysv_common

module Make(Context : Context_intf.S_virtual) = struct
  open Context.Syntax
  open Make0(Context)
  module Cv = Context.Virtual

  let expect_ret_var env l : operand -> Var.t Context.t = function
    | `var x -> !!x
    | x ->
      Context.failf
        "Expected var for `ret` operand in block %a \
         of function $%s, got %a" Label.pp l
        (Func.name env.fn) pp_operand x ()

  (* Return in the first integer register. *)
  let intret env key x =
    Context.return @@ Hashtbl.set env.rets ~key ~data:{
      reti = [];
      retr = [int_rets.(0), x];
    }

  (* Return in the first integer register, with a sign extension. *)
  let intret_signed env key x =
    let+ r, ri = Cv.Abi.unop (`sext `i64) x in
    Hashtbl.set env.rets ~key ~data:{
      reti = [ri];
      retr = [int_rets.(0), `var r];
    }

  (* Return in the first SSE register. *)
  let sseret env key x =
    Context.return @@ Hashtbl.set env.rets ~key ~data:{
      reti = [];
      retr = [sse_rets.(0), x];
    }

  (* Struct is returned in a single register. *)
  let onereg_ret env r key x =
    let* x = expect_ret_var env key x in
    let x = find_ref env x in
    let t = reg_type r in
    let reg = match t with
      | `i64 -> int_rets.(0)
      | `f64 -> sse_rets.(0) in
    let+ r, ri = Cv.Abi.load t (`var x) in
    Hashtbl.set env.rets ~key ~data:{
      reti = [ri];
      retr = [reg, `var r];
    }

  (* Struct is returned in two registers of varying classes. *)
  let tworeg_ret env r1 r2 key x =
    let* x = expect_ret_var env key x in
    let x = find_ref env x in
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let reg1, reg2 = match t1, t2 with
      | `i64, `i64 -> int_rets.(0), int_rets.(1)
      | `i64, `f64 -> int_rets.(0), sse_rets.(0)
      | `f64, `f64 -> sse_rets.(0), sse_rets.(1)
      | `f64, `i64 -> sse_rets.(0), int_rets.(0) in
    let* ld1, ldi1 = Cv.Abi.load t1 (`var x) in
    let* a, add = Cv.Abi.binop (`add `i64) (`var x) (i64 8) in
    let+ ld2, ldi2 = Cv.Abi.load t2 (`var a) in
    Hashtbl.set env.rets ~key ~data:{
      reti = [ldi1; add; ldi2];
      retr = [
        reg1, `var ld1;
        reg2, `var ld2;
      ];
    }

  (* Struct is blitted to a pointer held by by the implicit
     first argument of the function. This pointer becomes the
     return value. *)
  let memory_ret env k key x =
    let+ data = if k.size > 0 then
        let* x = expect_ret_var env key x in
        let dst = match env.rmem with
          | None -> assert false
          | Some dst -> dst in
        let retr = [int_rets.(0), `var dst] in
        (* In the case of `unref` we should've already blitted
           to `dst` (see Sysv_refs). *)
        let+ reti = if not @@ Hashtbl.mem env.unrefs x then
            let src = find_ref env x in
            Cv.Abi.blit `i64 k.size ~src ~dst
          else !![] in
        {reti; retr}
      else !!empty_ret in
    Hashtbl.set env.rets ~key ~data

  (* Lower the `ret` instructions. *)
  let lower env =
    let go f = iter_blks env ~f:(fun b -> match Blk.ctrl b with
        | `ret Some x -> f (Blk.label b) x
        | `ret None ->
          Context.failf
            "Expected return value in block %a of function $%s"
            Label.pp (Blk.label b) (Func.name env.fn) ()
        | _ -> !!()) in
    match Func.return env.fn with
    | None -> !!()
    | Some #Type.imm -> go @@ intret env
    | Some (`si8 | `si16 | `si32) -> go @@ intret_signed env
    | Some #Type.fp -> go @@ sseret env
    | Some `name n ->
      let* k = type_cls env n in
      match k.cls with
      | Kreg _ when k.size = 0 -> assert false
      | Kreg (r, _) when k.size = 8 -> go @@ onereg_ret env r
      | Kreg (r1, r2) -> go @@ tworeg_ret env r1 r2
      | Kmem -> go @@ memory_ret env k
end
