(* Implements the semantics of individual instructions. *)

open Core
open Regular.Std
open Virtual
open Sccp_intervals_common

external float_to_bits : float -> int64 = "cgen_bits_of_float"

let interp_const ctx : const -> I.t = function
  | `bool b -> I.boolean b
  | `int (value, t) -> I.create_single ~value ~size:(Type.sizeof_imm t)
  | `float f ->
    let value = Bv.M32.int32 @@ Float32.bits f in
    I.create_single ~value ~size:32
  | `double d ->
    let value = Bv.M64.int64 @@ float_to_bits d in
    I.create_single ~value ~size:64
  | `sym _ -> I.create_full ~size:(Type.sizeof_imm_base ctx.word)

let interp_operand ctx s : operand -> I.t option = function
  | #const as c -> Some (interp_const ctx c)
  | `var x -> match find_var s x with
    | Some _ as i -> i
    | None ->
      sizeof x ctx |> Option.map ~f:(fun size ->
          I.create_full ~size)

let interp_arith_binop o a b = match (o : Insn.arith_binop) with
  | `add #Type.imm -> I.add a b
  | `div #Type.imm -> I.sdiv a b
  | `mul #Type.imm -> I.mul a b
  | `mulh _ -> I.mulh a b
  | `umulh _ -> I.umulh a b
  | `rem #Type.imm -> I.srem a b
  | `sub #Type.imm -> I.sub a b
  | `udiv _ -> I.udiv a b
  | `urem _ -> I.urem a b
  | `add (#Type.fp as t)
  | `div (#Type.fp as t)
  | `mul (#Type.fp as t)
  | `rem (#Type.fp as t)
  | `sub (#Type.fp as t) ->
    I.create_full ~size:(Type.sizeof_fp t)

let interp_bitwise_binop o a b = match (o : Insn.bitwise_binop) with
  | `and_ _ -> I.logand a b
  | `or_ _ -> I.logor a b
  | `asr_ _ -> I.arithmetic_shift_right a b
  | `lsl_ _ -> I.logical_shift_left a b
  | `lsr_ _ -> I.logical_shift_right a b
  | `rol _ -> I.rotate_left a b
  | `ror _ -> I.rotate_right a b
  | `xor _ -> I.logxor a b

module Cmp_bool = Sccp_intervals_cmp_bool
module Cmp_constr = Sccp_intervals_cmp_constr

(* pre: If `l` and `r` are variables, then they are distinct. *)
let do_cmp ctx t x l r a b ~constr ~cmp =
  let sz = Type.sizeof_imm t in
  assert (I.size a = sz);
  assert (I.size b = sz);
  let il, ir = constr a b in
  Cmp_constr.set_constraint ctx x l il;
  Cmp_constr.set_constraint ctx x r ir;
  cmp a b

let interp_cmp ctx o x l r a b =
  (* Handle trivial case when the operands are equal. *)
  let eq = equal_operand l r in
  match (o : Insn.cmp) with
  | `eq  _ when eq -> I.boolean_true
  | `ne  _ when eq -> I.boolean_false
  | `lt  _ when eq -> I.boolean_false
  | `le  _ when eq -> I.boolean_true
  | `gt  _ when eq -> I.boolean_false
  | `ge  _ when eq -> I.boolean_true
  | `slt _ when eq -> I.boolean_false
  | `sle _ when eq -> I.boolean_true
  | `sgt _ when eq -> I.boolean_false
  | `sge _ when eq -> I.boolean_true
  | `eq (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.eq
      ~cmp:Cmp_bool.bool_eq
  | `ne (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.ne
      ~cmp:Cmp_bool.bool_ne
  | `lt (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.lt
      ~cmp:Cmp_bool.bool_lt
  | `le (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.le
      ~cmp:Cmp_bool.bool_le
  | `gt (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.gt
      ~cmp:Cmp_bool.bool_gt
  | `ge (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.ge
      ~cmp:Cmp_bool.bool_ge
  | `slt t ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.slt
      ~cmp:(Cmp_bool.bool_slt t)
  | `sle t ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.sle
      ~cmp:(Cmp_bool.bool_sle t)
  | `sgt t ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.sgt
      ~cmp:(Cmp_bool.bool_sgt t)
  | `sge t ->
    do_cmp ctx t x l r a b
      ~constr:Cmp_constr.sge
      ~cmp:(Cmp_bool.bool_sge t)
  | `eq #Type.fp
  | `ne #Type.fp
  | `lt #Type.fp
  | `le #Type.fp
  | `gt #Type.fp
  | `ge #Type.fp
  | `o _
  | `uo _ -> I.boolean_full

let div_rem_self l r b =
  equal_operand l r && not (I.contains_value b Bv.zero)

let interp_binop ctx o x l r a b = match (o : Insn.binop) with
  | #Insn.arith_binop as o ->
    (* Special case for division by self. *)
    begin match o with
      | `div (#Type.imm as t) | `udiv t when div_rem_self l r b ->
        I.create_single ~value:Bv.one ~size:(Type.sizeof_imm t)
      | `rem (#Type.imm as t) | `urem t when div_rem_self l r b ->
        I.create_single ~value:Bv.zero ~size:(Type.sizeof_imm t)
      | _ -> interp_arith_binop o a b
    end
  | #Insn.bitwise_binop as o -> interp_bitwise_binop o a b
  | #Insn.cmp as o -> interp_cmp ctx o x l r a b

let interp_arith_unop o a = match (o : Insn.arith_unop) with
  | `neg _ -> I.neg a

let interp_bitwise_unop o a = match (o : Insn.bitwise_unop) with
  | `clz _ -> I.clz a
  | `ctz _ -> I.ctz a
  | `popcnt _ -> I.popcnt a
  | `not_ _ -> I.lnot a

let interp_cast o a = match (o : Insn.cast) with
  | `fext t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) ->
    I.create_full ~size:(Type.sizeof_fp t)
  | `fibits _ | `ifbits _ -> a
  | `flag t | `zext t ->
    I.zext a ~size:(Type.sizeof_imm t)
  | `ftosi (_, t)
  | `ftoui (_, t) ->
    I.create_full ~size:(Type.sizeof_imm t)
  | `itrunc t ->
    I.trunc a ~size:(Type.sizeof_imm t)
  | `sext t ->
    I.sext a ~size:(Type.sizeof_imm t)

let interp_copy o a = match (o : Insn.copy) with
  | `copy _ -> a

let interp_unop o a = match (o : Insn.unop) with
  | #Insn.arith_unop as o -> interp_arith_unop o a
  | #Insn.bitwise_unop as o -> interp_bitwise_unop o a
  | #Insn.cast as o -> interp_cast o a
  | #Insn.copy as o -> interp_copy o a

let try1 s x ~f =
  Option.value_map x ~default:s ~f

let try2 s x y ~f =
  Option.both x y |>
  Option.value_map ~default:s ~f

let interp_basic_binop ctx s x o l r =
  let a = interp_operand ctx s l in
  let b = interp_operand ctx s r in
  try2 s a b ~f:(fun (a, b) ->
      update s x @@ interp_binop ctx o x l r a b)

let interp_basic_unop ctx s x o a =
  interp_operand ctx s a |> try1 s ~f:(fun a ->
      interp_unop o a |> update s x)

let interp_basic_sel ctx s x k y n =
  interp_operand ctx s (`var k) |> try1 s ~f:(fun c ->
      let y, n = match Hashtbl.find ctx.cond k with
        | Some s' ->
          interp_operand ctx (meet_state s s') y,
          interp_operand ctx (meet_state s @@ invert_state s') n
        | None ->
          interp_operand ctx s y,
          interp_operand ctx s n in
      try2 s y n ~f:(fun (y, n) ->
          update s x @@ match I.single_of c with
          | None -> I.union y n
          | Some i when Bv.(i = zero) -> n
          | Some _ -> y))

let interp_basic ctx s : Insn.basic -> state = function
  | `bop (x, o, l, r) -> interp_basic_binop ctx s x o l r
  | `uop (x, o, a) -> interp_basic_unop ctx s x o a
  | `sel (x, _, k, y, n) -> interp_basic_sel ctx s x k y n

let make_top s x = function
  | #Type.basic as t ->
    update s x @@ I.create_full ~size:(Type.sizeof_basic t)
  | `si8 -> update s x @@ I.create_full ~size:8
  | `si16 -> update s x @@ I.create_full ~size:16
  | `si32 -> update s x @@ I.create_full ~size:32
  | `name _ -> s

let interp_call _ctx s : Insn.call -> state = function
  | `call (Some (x, t), _, _, _) -> make_top s x t
  | `call (None, _, _, _) -> s

(* TODO: maybe model memory? *)
let interp_mem _ctx s : Insn.mem -> state = function
  | `load (x, (#Type.basic as t), _) -> make_top s x t
  | `load _ | `store _ -> s

let interp_variadic _ s : Insn.variadic -> state = function
  | `vaarg (x, t, _) -> make_top s x t
  | `vastart _ -> s

let interp_insn ctx s i =
  let s = match Insn.op i with
    | #Insn.basic as b -> interp_basic ctx s b
    | #Insn.call as c -> interp_call ctx s c
    | #Insn.mem as m -> interp_mem ctx s m
    | #Insn.variadic as v -> interp_variadic ctx s v in
  Hashtbl.set ctx.insns ~key:(Insn.label i) ~data:s;
  s

let assign_blk_args ctx s l args =
  match Label.Tree.find ctx.blks l with
  | None -> s
  | Some b ->
    let args' = Blk.args b |> Seq.to_list in
    match List.zip args args' with
    | Unequal_lengths -> s
    | Ok xs -> List.fold xs ~init:s ~f:(fun s (o, x) ->
        interp_operand ctx s o |> try1 s ~f:(update_union s x))

(* The empty and full intervals don't carry any interesting
   information about a possible branch condition, and may
   lead to unsound approximations when propagated. *)
module Narrow_branch = struct
  let has_info i = not I.(is_full i || is_empty i)

  let default s x i = match Map.find s x with
    | None -> I.create_full ~size:(I.size i)
    | Some i -> i

  let both ctx s y n x i =
    if has_info i then
      let i' = I.inverse i in
      narrow ctx y x i;
      narrow ctx n x i'
    else
      let i = default s x i in
      narrow ctx y x i;
      narrow ctx n x i

  let yes ctx s y x i =
    narrow ctx y x @@
    if has_info i then i
    else default s x i

  let no ctx s n x i =
    narrow ctx n x @@
    if has_info i
    then I.inverse i
    else default s x i
end

let interp_ctrl ctx s = function
  | `jmp `label (l, args) ->
    assign_blk_args ctx s l args
  | `br (c, `label (y, yargs), `label (n, nargs)) ->
    narrow ctx y c I.boolean_true;
    narrow ctx n c I.boolean_false;
    Hashtbl.find ctx.cond c |> Option.iter ~f:(fun s' ->
        Map.iteri s' ~f:(fun ~key:x ~data:i ->
            Narrow_branch.both ctx s y n x i));
    let s = assign_blk_args ctx s y yargs in
    assign_blk_args ctx s n nargs
  | `br (c, `label (y, yargs), _) ->
    narrow ctx y c I.boolean_true;
    Hashtbl.find ctx.cond c |> Option.iter ~f:(fun s' ->
        Map.iteri s' ~f:(fun ~key:x ~data:i ->
            Narrow_branch.yes ctx s y x i));
    assign_blk_args ctx s y yargs
  | `br (c, _, `label (n, nargs)) ->
    narrow ctx n c I.boolean_false;
    Hashtbl.find ctx.cond c |> Option.iter ~f:(fun s' ->
        Map.iteri s' ~f:(fun ~key:x ~data:i ->
            Narrow_branch.no ctx s n x i));
    assign_blk_args ctx s n nargs
  | `sw (t, `var x, `label (d, args), tbl) ->
    let size = Type.sizeof_imm t in
    let s =
      (* XXX: the set of known values for `x` in each arm
         of the switch may be disjoint, so we settle for
         an overapproximation of `x` in the default case. *)
      Ctrl.Table.enum tbl |>
      Seq.fold ~init:s ~f:(fun s (v, `label (l, args)) ->
          if Label.(l <> d) then
            (* Don't narrow for the default case. *)
            narrow ctx l x @@ I.create_single ~value:v ~size;
          assign_blk_args ctx s l args) in
    assign_blk_args ctx s d args
  | _ -> s

(* Our transfer function. *)
let interp_blk ctx s b =
  Blk.insns b |>
  Seq.fold ~init:s ~f:(interp_insn ctx) |>
  Fn.flip (interp_ctrl ctx) (Blk.ctrl b)
