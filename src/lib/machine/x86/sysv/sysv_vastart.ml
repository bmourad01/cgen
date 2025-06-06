open Core
open Virtual
open Sysv_common

let ap_oper : global -> operand = function
  | `addr a -> `int (a, `i64)
  | `sym _ as s -> s
  | `var _ as v -> v

module Make(Context : Context_intf.S_virtual) = struct
  open Context.Syntax
  open Make0(Context)
  module Cv = Context.Virtual

  (* Initialize the `va_list` structure, which is defined as follows:

     typedef struct {
       unsigned int gp_offset;
       unsigned_int fp_offset;
       void *overflow_arg_area;
       void *reg_save_area;
     } va_list[1];

     where

     `gp_offset` and `fp_offset` are the offsets into the register
     save area for the next available integer and SSE registers,
     respectively

     `overflow_arg_area` is a pointer to the next available parameter
     that was passed on the stack

     `reg_save_area` is the start of the register save area
  *)
  let lower env = match env.rsave with
    | None -> !!()
    | Some rs -> iter_blks env ~f:(fun b ->
        Blk.insns b |> Context.Seq.iter ~f:(fun i ->
            match Insn.op i with
            | `vastart ap ->
              let ap = ap_oper ap in
              (* Compute `gp_offset` and `fp_offset`. *)
              let gp, fp =
                Vec.fold env.params ~init:(0, 48) ~f:(fun (gp, fp) p ->
                    match p.pvar, p.pty with
                    | `reg _, #Type.imm -> gp + 8, fp
                    | `reg _, #Type.fp -> gp, fp + 16
                    | `stk _, _ -> gp, fp) in
              (* Initialize `gp_offset`. *)
              let* gpi = Cv.Abi.store `i32 (i32 gp) ap in
              (* Initialize `fp_offset`. *)
              let* o, oi1 = Cv.Abi.binop (`add `i64) ap (i64 4) in
              let* fpi = Cv.Abi.store `i32 (i32 fp) (`var o) in
              (* Initialize `overflow_arg_area`. *)
              let* r, ri = Cv.Abi.stkargs () in
              let* o, oi2 = Cv.Abi.binop (`add `i64) ap (i64 8) in
              let* ofi = Cv.Abi.store `i64 (`var r) (`var o) in
              (* Initialize `reg_save_area`. *)
              let* o, oi3 = Cv.Abi.binop (`add `i64) ap (i64 16) in
              let+ rs = Cv.Abi.store `i64 (`var rs.rsslot) (`var o) in
              (* Store the result. *)
              Hashtbl.set env.vastart ~key:(Insn.label i) ~data:[
                gpi; oi1; fpi; ri; oi2; ofi; oi3; rs;
              ]
            | _ -> !!()))
end
