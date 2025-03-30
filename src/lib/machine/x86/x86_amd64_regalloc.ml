(* Helpers required by the implementations in [Regalloc]. *)

open Core
open X86_amd64_common
open Insn

(* XXX: any more cases than this? *)
let copy = function
  | Two (MOV, Oreg (d, td), Oreg (s, ts))
  | Two (MOVSS, Oreg (d, td), Oreg (s, ts))
  | Two (MOVSD, Oreg (d, td), Oreg (s, ts))
    when Type.equal_basic td ts -> Some (d, s)
  | _ -> None

let classof rv = match Regvar.which rv with
  | First r -> Reg.classof r
  | Second (_, cls) -> cls

let load_from_slot ty ~dst ~src = match classof dst with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b -> I.mov (Oreg (dst, b)) (Omem (Ab src, b))
    end
  | FP ->
    begin match ty with
      | `f64 -> I.movsd (Oreg (dst, `f64)) (Omem (Ab src, `i64))
      | `f32 -> I.movss (Oreg (dst, `f32)) (Omem (Ab src, `i32))
      | `v128 -> I.movdqa (Oregv dst) (Omem (Ab src, `v128))
      | #Type.imm -> assert false
    end

let store_to_slot ty ~src ~dst = match classof src with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b -> I.mov (Omem (Ab dst, b)) (Oreg (src, b))
    end
  | FP ->
    begin match ty with
      | `f64 -> I.movsd (Omem (Ab dst, `i64)) (Oreg (src, `f64))
      | `f32 -> I.movss (Omem (Ab dst, `i32)) (Oreg (src, `f32))
      | `v128 -> I.movdqa (Omem (Ab dst, `v128)) (Oregv src)
      | #Type.imm -> assert false
    end

let substitute_amode f = function
  | Ad _ as a -> a
  | Ab b -> Ab (f b)
  | Abd (b, d) -> Abd (f b, d)
  | Abis (b, i, s) -> Abis (f b, f i, s)
  | Aisd (i, s, d) -> Aisd (f i, s, d)
  | Abisd (b, i, s, d) -> Abisd (f b, f i, s, d)

let substitute_operand f = function
  | Oreg (r, t) -> Oreg (f r, t)
  | Oregv v -> Oregv (f v)
  | Oimm _ as i -> i
  | Omem (a, ty) -> Omem (substitute_amode f a, ty)
  | Osym _ as s -> s
  | Ofp32 _ as s -> s
  | Ofp64 _ as d -> d
  | Oah -> Oah

let substitute' i op = match i with
  | One (o, a) -> One (o, op a)
  | Two (o, a, b) -> Two (o, op a, op b)
  | IMUL3 (a, b, c) -> IMUL3 (op a, op b, c)
  | CDQ
  | CQO
  | CWD
  | Jcc _
  | JMP _
  | RET
  | UD2
  | JMPtbl _ -> i

let substitute i f = substitute' i @@ substitute_operand f

module Typed_writes = struct
  type ty = [Type.basic | `v128]

  let wty ty = (ty :> ty)

  let reduce a b = match a, b with
    | (#Type.imm as ia), (#Type.imm as ib)
      when Type.sizeof_imm ia < Type.sizeof_imm ib -> b
    | #Type.imm, #Type.imm -> a
    | (#Type.fp as fa), (#Type.fp as fb)
      when Type.sizeof_fp fa < Type.sizeof_fp fb -> b
    | #Type.fp, #Type.fp -> a
    | `v128, `v128 -> `v128
    | _ -> assert false

  (* Helper for registers mentioned in an addressing mode. *)
  let rv_of_amode = function
    | Ad _ -> []
    | Ab a -> [a, `i64]
    | Abd (a, _) -> [a, `i64]
    | Abis (a, b, _) -> [a, `i64; b, `i64]
    | Aisd (a, _, _) -> [a, `i64]
    | Abisd (a, b, _, _) -> [a, `i64; b, `i64]

  (* All registers mentioned in operands. *)
  let rmap operands =
    Regvar.Map.of_alist_reduce ~f:reduce @@
    List.bind operands ~f:(function
        | Oreg (a, t) -> [a, wty t]
        | Oregv a -> [a, `v128]
        | Omem (a, _) -> rv_of_amode a
        | Oah -> [Regvar.reg `rax, wty `i8]
        | _ -> [])

  (* Only explicit register operands. *)
  let rmap_reg operands =
    Regvar.Map.of_alist_reduce ~f:reduce @@
    List.bind operands ~f:(function
        | Oreg (a, t) -> [a, wty t]
        | Oregv a -> [a, `v128]
        | Oah -> [Regvar.reg `rax, `i8]
        | _ -> [])

  let rmap' l =
    Regvar.Map.of_alist_reduce ~f:reduce @@
    List.map l ~f:(fun (r, t) -> Regvar.reg r, t)

  (* Registers written to by an instruction. *)
  let writes call = function
    | Two (o, a, _) ->
      begin match o with
        | ADD
        | ADDSD
        | ADDSS
        | AND
        | CMOVcc _
        | CVTSD2SI
        | CVTSD2SS
        | CVTSI2SD
        | CVTSI2SS
        | CVTSS2SD
        | CVTSS2SI
        | DIVSD
        | DIVSS
        | IMUL2
        | LEA
        | LZCNT
        | MOV
        | MOV_
        | MOVD
        | MOVDQA
        | MOVQ
        | MOVSD
        | MOVSS
        | MOVSX
        | MOVSXD
        | MOVZX
        | MULSD
        | MULSS
        | OR
        | POPCNT
        | ROL
        | ROR
        | SAR
        | SHL
        | SHR
        | SUB
        | SUBSD
        | SUBSS
        | TZCNT
        | XOR
        | XORPD
        | XORPS
          -> rmap_reg [a]
        | CMP
        | TEST_
        | UCOMISD
        | UCOMISS
          -> Regvar.Map.empty
      end
    | One (o, a) ->
      begin match o with
        | CALL
          -> call
        | DEC
        | INC
        | NEG
        | NOT
        | SETcc _
        | POP
          -> rmap_reg [a]
        | PUSH
          -> Regvar.Map.empty
        | DIV
        | IDIV
        | IMUL1
        | MUL ->
          begin match a with
            | Oreg (_, `i8)
              -> rmap' [`rax, `i8]
            | Oreg (_, t)
              -> rmap' [`rax, wty t; `rdx, wty t]
            | Omem (_, t)
              -> rmap' [`rax, wty t; `rdx, wty t]
            | _
              (* invalid forms *)
              -> Regvar.Map.empty
          end
      end
    | IMUL3 (a, _, _)
      -> rmap_reg [a]
    | Jcc _
    | JMP _
    | JMPtbl _
    | RET
    | UD2
      -> Regvar.Map.empty
    | CDQ
      -> rmap' [`rdx, `i32]
    | CQO
      -> rmap' [`rdx, `i64]
    | CWD
      -> rmap' [`rdx, `i16]
end

let writes_with_types = Typed_writes.writes

module Replace_direct_slot_uses(C : Context_intf.S) = struct
  open C.Syntax

  let replace_amode is_slot a = match a with
    | Abis (b, i, s) when is_slot i ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Abis (b, x, s), [I.lea (Oreg (x, `i64)) (Omem (Ab i, `i64))]
    | Aisd (i, s, d) when is_slot i ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Aisd (x, s, d), [I.lea (Oreg (x, `i64)) (Omem (Ab i, `i64))]
    | Abisd (b, i, s, d) when is_slot i ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Abisd (b, x, s, d), [I.lea (Oreg (x, `i64)) (Omem (Ab i, `i64))]
    | _ -> !!(a, [])

  let replace_operand is_slot op = match op with
    | Oreg (r, ty) when is_slot r ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Oreg (x, ty), [I.lea (Oreg (x, ty)) (Omem (Ab r, `i64))]
    | Oreg _ -> !!(op, [])
    | Omem (a, ty) ->
      let+ a, ai = replace_amode is_slot a in
      Omem (a, ty), ai
    | _ -> !!(op, [])

  let replace is_slot i =
    let op = replace_operand is_slot in
    match i with
    | One (o, a) ->
      let+ a, ai = op a in
      ai @ [One (o, a)]
    | Two (o, a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [Two (o, a, b)]
    | IMUL3 (a, b, c) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [IMUL3 (a, b, c)]
    | JMP (Jind a) ->
      let+ a, ai = op a in
      ai @ [JMP (Jind a)]
    | CDQ
    | CQO
    | CWD
    | Jcc _
    | JMP _
    | RET
    | UD2
    | JMPtbl _ -> !![i]
end

module Assign_slots = struct
  let find offsets rv = match Regvar.which rv with
    | Second (v, _) -> Map.find offsets v
    | First _ -> None

  (* XXX: fix this to account for overflow *)
  let add_disp off = function
    | Dsym (s, o) -> Dsym (s, o + off)
    | Dimm i -> Dimm Int32.(i + of_int_exn off)
    | Dlbl _ -> assert false

  let idisp i = Dimm (Int32.of_int_exn i)

  let assign_amode base offsets a = match a with
    | Ad _d -> a
    | Ab b ->
      begin match find offsets b with
        | Some 0 -> Ab base
        | Some o -> Abd (base, idisp o)
        | None -> a
      end
    | Abd (b, d) ->
      begin match find offsets b with
        | Some o -> Abd (base, add_disp o d)
        | None -> a
      end
    | Abis (b, i, s) ->
      begin match find offsets b, find offsets i with
        | None, None -> a
        | Some 0, None -> Abis (base, i, s)
        | Some o, None -> Abisd (base, i, s, idisp o)
        | _, Some _ -> assert false
      end
    | Aisd (i, _s, _d) ->
      begin match find offsets i with
        | None -> a
        | Some _ -> assert false
      end
    | Abisd (b, i, s, d) ->
      begin match find offsets b, find offsets i with
        | None, None -> a
        | Some o, None -> Abisd (base, i, s, add_disp o d)
        | _, Some _ -> assert false
      end

  let assign_operand base offsets op = match op with
    | Oreg (r, _) ->
      begin match find offsets r with
        | None -> op
        | Some _ -> assert false
      end
    | Oregv r ->
      begin match find offsets r with
        | None -> op
        | Some _ -> assert false
      end
    | Omem (a, ty) -> Omem (assign_amode base offsets a, ty)
    | _ -> op

  let assign base offsets i =
    let base = Regvar.reg base in
    substitute' i @@ assign_operand base offsets
end

let assign_slots = Assign_slots.assign

let align8 i = (i + 7) land -8
let odd i = (i land 1) <> 0
let is16 i = (i land 15) = 0

(* Pad the stack to account for:

   1. The return address already on the stack upon entry.
   2. The callee-save registers being pushed to the stack.
*)
let adjust_sp_size regs size = match List.length regs with
  | 0 when is16 size -> size + 8
  | 0 -> size
  | n when odd n && is16 size -> size
  | n when odd n -> size + 8
  | _ when is16 size -> size + 8
  | _ -> size

let no_frame_prologue regs size =
  let size = Int64.of_int @@ adjust_sp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  List.concat [
    List.map regs ~f:(fun r ->
        I.push (Oreg (Regvar.reg r, `i64)));
    (if Int64.(size = 0L) then []
     else [I.sub rsp (Oimm (size, `i64))]);
  ]

let no_frame_epilogue regs size =
  let size = Int64.of_int @@ adjust_sp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  List.concat [
    (if Int64.(size = 0L) then []
     else [I.add rsp (Oimm (size, `i64))]);
    List.rev regs |> List.map ~f:(fun r ->
        I.pop (Oreg (Regvar.reg r, `i64)));
  ]

(* Same as above, but with the added factor of the frame
   pointer being pushed to the stack.

   This amounts to adding 8 in the opposite cases.
*)
let adjust_fp_size regs size = match List.length regs with
  | 0 when is16 size -> size
  | 0 -> size + 8
  | n when odd n && is16 size -> size + 8
  | n when odd n -> size
  | _ when is16 size -> size
  | _ -> size + 8

let frame_prologue regs size =
  let size = Int64.of_int @@ adjust_fp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  let rbp = Oreg (Regvar.reg `rbp, `i64) in
  List.concat [
    (* Push the frame pointer and give it the base of the stack. *)
    [I.push rbp;
     I.mov rbp rsp];
    (* Allocate space. *)
    (if Int64.(size = 0L) then []
     else [I.sub rsp (Oimm (size, `i64))]);
    (* Push the callee-save registers. *)
    List.map regs ~f:(fun r ->
        I.push (Oreg (Regvar.reg r, `i64)));
  ]

let frame_epilogue regs size =
  let size = Int64.of_int @@ adjust_fp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  let rbp = Oreg (Regvar.reg `rbp, `i64) in
  List.concat [
    (* Pop the callee-save registers in reverse order. *)
    List.rev regs |> List.map ~f:(fun r ->
        I.pop (Oreg (Regvar.reg r, `i64)));
    (* Deallocate space. *)
    (if Int64.(size = 0L) then []
     else [I.add rsp (Oimm (size, `i64))]);
    (* Pop the frame pointer. *)
    [I.pop rbp];
  ]
