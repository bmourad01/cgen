open Core
open Regular.Std
open Graphlib.Std
open Common

module I = Bv_interval

type state = I.t Var.Map.t [@@deriving equal, sexp]

let empty_state : state = Var.Map.empty

let join_state x y =
  Map.merge_skewed x y ~combine:(fun ~key:_ a b -> I.union a b)

let meet_state x y =
  Map.merge_skewed x y ~combine:(fun ~key:_ a b -> I.intersect a b)

let update s x i = Map.update s x ~f:(function
    | Some i' -> I.union i i'
    | None -> i)

let find_var = Map.find
let enum_state s = Map.to_sequence s

type info = {
  constr : state Label.Table.t;
  param  : int Var.Table.t;
  blks   : Blk.t Label.Tree.t;
  word   : Type.imm_base;
  typeof : Var.t -> Type.t;
}

let create_info ~blks ~word ~typeof = {
  constr = Label.Table.create ();
  param = Var.Table.create ();
  blks;
  word;
  typeof;
}

let update_constr info l x i =
  Hashtbl.update info.constr l ~f:(function
      | None -> Var.Map.singleton x i
      | Some s -> update s x i)

let interp_const info : const -> I.t = function
  | `bool b -> I.boolean b
  | `int (value, t) -> I.create_single ~value ~size:(Type.sizeof_imm t)
  | `float f ->
    let value = Bv.M32.int32 @@ Float32.bits f in
    I.create_single ~value ~size:32
  | `double d ->
    let value = Bv.M64.int64 @@ Eval.float_to_bits d in
    I.create_single ~value ~size:64
  | `sym _ -> I.create_full ~size:(Type.sizeof_imm_base info.word)

let sizeof x info = match info.typeof x with
  | #Type.basic as b -> Type.sizeof_basic b
  | `flag -> 1
  | _ -> Type.sizeof_imm_base info.word

let interp_operand info s : operand -> I.t = function
  | #const as c -> interp_const info c
  | `var x -> match find_var s x with
    | None -> I.create_full ~size:(sizeof x info)
    | Some i -> i

let interp_arith_binop o a b = match (o : Insn.arith_binop) with
  | `add #Type.imm -> I.add a b
  | `div #Type.imm -> I.sdiv a b
  | `mul #Type.imm -> I.mul a b
  | `mulh t | `umulh t -> I.create_full ~size:(Type.sizeof_imm t) (* TODO *)
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
  | `rol t | `ror t -> I.create_full ~size:(Type.sizeof_imm t) (* TODO *)
  | `xor _ -> I.logxor a b

let interp_cmp o a b = match (o : Insn.cmp) with
  | `eq #Type.imm ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b -> I.boolean Bv.(a = b)
    end
  | `ne #Type.imm ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b -> I.boolean Bv.(a <> b)
    end
  | `lt #Type.imm ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b -> I.boolean Bv.(a < b)
    end
  | `le #Type.imm ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b -> I.boolean Bv.(a <= b)
    end
  | `gt #Type.imm ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b -> I.boolean Bv.(a > b)
    end
  | `ge #Type.imm ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b -> I.boolean Bv.(a >= b)
    end
  | `slt t ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b ->
        let m = Bv.modulus @@ Type.sizeof_imm t in
        I.boolean (Bv.signed_compare a b m < 0)
    end
  | `sle t ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b ->
        let m = Bv.modulus @@ Type.sizeof_imm t in
        I.boolean (Bv.signed_compare a b m <= 0)
    end
  | `sgt t ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b ->
        let m = Bv.modulus @@ Type.sizeof_imm t in
        I.boolean (Bv.signed_compare a b m > 0)
    end
  | `sge t ->
    begin match I.(single_of a, single_of b) with
      | None, _ | _, None -> I.boolean_full
      | Some a, Some b ->
        let m = Bv.modulus @@ Type.sizeof_imm t in
        I.boolean (Bv.signed_compare a b m >= 0)
    end
  | `eq #Type.fp
  | `ne #Type.fp
  | `lt #Type.fp
  | `le #Type.fp
  | `gt #Type.fp
  | `ge #Type.fp
  | `o _
  | `uo _ -> I.boolean_full

let interp_binop o a b = match (o : Insn.binop) with
  | #Insn.arith_binop as o -> interp_arith_binop o a b
  | #Insn.bitwise_binop as o -> interp_bitwise_binop o a b
  | #Insn.cmp as o -> interp_cmp o a b

let interp_arith_unop o a = match (o : Insn.arith_unop) with
  | `neg _ -> I.neg a

let interp_bitwise_unop o a = match (o : Insn.bitwise_unop) with
  | `clz t | `ctz t | `popcnt t -> I.create_full ~size:(Type.sizeof_imm t)
  | `not_ _ -> I.lnot a

let interp_cast o a = match (o : Insn.cast) with
  | `fext t
  | `fibits t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) ->
    I.create_full ~size:(Type.sizeof_fp t)
  | `flag t | `zext t ->
    I.zext a ~size:(Type.sizeof_imm t)
  | `ftosi (_, t)
  | `ftoui (_, t) ->
    I.create_full ~size:(Type.sizeof_imm t)
  | `ifbits t ->
    I.create_full ~size:(Type.sizeof_imm_base t)
  | `itrunc t ->
    I.trunc a ~size:(Type.sizeof_imm t)
  | `sext t ->
    I.sext a ~size:(Type.sizeof_imm t)

let interp_copy o a = match (o : Insn.copy) with
  | `copy _ -> a
  | `ref t -> I.create_full ~size:(Type.sizeof_imm_base t)

let interp_unop o a = match (o : Insn.unop) with
  | #Insn.arith_unop as o -> interp_arith_unop o a
  | #Insn.bitwise_unop as o -> interp_bitwise_unop o a
  | #Insn.cast as o -> interp_cast o a
  | #Insn.copy as o -> interp_copy o a

let interp_basic info s : Insn.basic -> state = function
  | `bop (x, o, a, b) ->
    let a = interp_operand info s a in
    let b = interp_operand info s b in
    update s x @@ interp_binop o a b
  | `uop (x, o, a) ->
    let a = interp_operand info s a in
    update s x @@ interp_unop o a
  | `sel (x, _, c, y, n) ->
    let c = interp_operand info s @@ `var c in
    let y = interp_operand info s y in
    let n = interp_operand info s n in
    let r = match I.single_of c with
      | None -> I.union y n
      | Some i when Bv.(i = zero) -> n
      | Some _ -> y in
    update s x r

let make_top s x t =
  update s x @@ I.create_full ~size:(Type.sizeof_basic t)

let interp_call _ s : Insn.call -> state = function
  | `call (Some (x, t), _, _, _) -> make_top s x t
  | `call (None, _, _, _) -> s

(* TODO: maybe model memory? *)
let interp_mem _ s : Insn.mem -> state = function
  | `load (x, t, _) -> make_top s x t
  | `store _ -> s

let interp_variadic _ s : Insn.variadic -> state = function
  | `vaarg (x, t, _) -> make_top s x t
  | `vastart _ -> s

let interp_insn info s i = match Insn.op i with
  | #Insn.basic as b -> interp_basic info s b
  | #Insn.call as c -> interp_call info s c
  | #Insn.mem as m -> interp_mem info s m
  | #Insn.variadic as v -> interp_variadic info s v

let incr_param info x =
  let n = ref 0 in
  Hashtbl.update info.param x ~f:(function
      | None -> !n
      | Some i ->
        let i = i + 1 in
        n := i;
        i);
  !n

let constr_params info s l args =
  match Label.Tree.find info.blks l with
  | None -> s
  | Some b ->
    let args' = Blk.args b |> Seq.to_list in
    match List.zip args args' with
    | Unequal_lengths -> s
    | Ok xs -> List.fold xs ~init:s ~f:(fun s (o, x) ->
        (* This could be improved, but it's a start. *)
        update s x @@ if incr_param info x > 10
        then I.create_full ~size:(sizeof x info)
        else interp_operand info s o)

let interp_blk info s b =
  let s = match Hashtbl.find info.constr @@ Blk.label b with
    | Some s' -> meet_state s' s
    | None -> s in
  let s =
    Blk.insns b |>
    Seq.fold ~init:s ~f:(interp_insn info) in
  match Blk.ctrl b with
  | `jmp `label (l, args) ->
    constr_params info s l args
  | `br (_, `label (y, yargs), `label (n, nargs)) ->
    let s = constr_params info s y yargs in
    constr_params info s n nargs
  | `br (_, `label (y, yargs), _) ->
    constr_params info s y yargs
  | `br (_, _, `label (n, nargs)) ->
    constr_params info s n nargs
  | `sw (t, `var x, `label (d, args), tbl) ->
    let size = Type.sizeof_imm t in
    let s, all =
      Ctrl.Table.enum tbl |>
      Seq.fold ~init:(s, I.create_empty ~size)
        ~f:(fun (s, i) (v, `label (l, args)) ->
            let k = I.create_single ~value:v ~size in
            update_constr info l x k;
            let s = constr_params info s l args in
            s, I.union i k) in
    update_constr info d x @@ I.inverse all;
    constr_params info s d args
  | _ -> s

let init_state info fn =
  let init =
    Func.args fn |> Seq.fold ~init:empty_state ~f:(fun s (x, _) ->
        let data = I.create_full ~size:(sizeof x info) in
        Map.set s ~key:x ~data) in
  let init =
    Func.slots fn |> Seq.fold ~init ~f:(fun s x ->
        let data = I.create_full ~size:(Type.sizeof_imm_base info.word) in
        Map.set s ~key:(Func.Slot.var x) ~data) in
  Solution.create Label.(Map.singleton pseudoentry init) init

let transfer info l s = match Label.Tree.find info.blks l with
  | Some b -> interp_blk info s b
  | None -> s

let cyclomatic_complexity cfg =
  let e = Cfg.number_of_edges cfg in
  let n = Cfg.number_of_nodes cfg in
  e - n + 2

(* Scale the cyclomatic complecity by some number to increase
   the precision of the results. *)
let scale = 42

let analyze ?steps fn ~word ~typeof =
  let cfg = Cfg.create fn in
  let steps = match steps with
    | None -> cyclomatic_complexity cfg * scale
    | Some n -> n in
  let blks = Func.map_of_blks fn in
  let info = create_info ~blks ~word ~typeof in
  Graphlib.fixpoint (module Cfg) cfg ~steps
    ~init:(init_state info fn)
    ~equal:equal_state
    ~merge:join_state
    ~f:(transfer info)
