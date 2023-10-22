(* This analysis performs abstract interpretation in the usual
   Kildall fixpoint loop, where our abstract domain is contiguous
   intervals of bitvectors.

   This does not capture the semantics of floating point numbers,
   which would require its own abstract domain (likely orders of
   magnitude more complicated than BV intervals). Thus in most
   cases we settle for overapproximation.

   Additionally, we avoid modeling memory for now to keep things
   relatively simple.
*)

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

let invert_state = Map.map ~f:I.inverse

let update s x i = Map.update s x ~f:(function
    | Some i' -> I.union i i'
    | None -> i)

let find_var = Map.find
let enum_state s = Map.to_sequence s

type ctx = {
  insns  : state Label.Table.t;
  narrow : state Label.Table.t;
  cond   : state Var.Table.t;
  blks   : Blk.t Label.Tree.t;
  word   : Type.imm_base;
  typeof : Var.t -> Type.t;
}

let create_ctx ~blks ~word ~typeof = {
  insns = Label.Table.create ();
  narrow = Label.Table.create ();
  cond = Var.Table.create ();
  blks;
  word;
  typeof;
}

let narrow ctx l x i = Hashtbl.update ctx.narrow l ~f:(function
    | None -> Var.Map.singleton x i
    | Some s -> update s x i)

let interp_const ctx : const -> I.t = function
  | `bool b -> I.boolean b
  | `int (value, t) -> I.create_single ~value ~size:(Type.sizeof_imm t)
  | `float f ->
    let value = Bv.M32.int32 @@ Float32.bits f in
    I.create_single ~value ~size:32
  | `double d ->
    let value = Bv.M64.int64 @@ Eval.float_to_bits d in
    I.create_single ~value ~size:64
  | `sym _ -> I.create_full ~size:(Type.sizeof_imm_base ctx.word)

let sizeof x ctx = match ctx.typeof x with
  | #Type.basic as b -> Some (Type.sizeof_basic b)
  | #Type.compound -> None
  | `flag -> Some 1

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

(* Helpers for dealing with comparisons. *)
module Cmp = struct
  let bool_eq a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean Bv.(a = b)
    | _ when I.(is_empty @@ intersect a b) -> I.boolean_false
    | _ -> I.boolean_full

  let bool_ne a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean Bv.(a <> b)
    | _ when I.(is_empty @@ intersect a b) -> I.boolean_true
    | _ -> I.boolean_full

  let umin = I.unsigned_min
  let umax = I.unsigned_max

  let less f a b =
    if f (umax a) (umin b) then I.boolean_true
    else if not (f (umin a) (umax b)) then I.boolean_false
    else I.boolean_full

  let greater f a b =
    if f (umin a) (umax b) then I.boolean_true
    else if not (f (umax a) (umin b)) then I.boolean_false
    else I.boolean_full

  let bool_lt a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean Bv.(a < b)
    | _ -> less Bv.(<) a b

  let bool_le a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean Bv.(a <= b)
    | _ -> less Bv.(<=) a b

  let bool_gt a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean Bv.(a > b)
    | _ -> greater Bv.(>) a b

  let bool_ge a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean Bv.(a >= b)
    | _ -> greater Bv.(>=) a b

  let scmp t a b = Bv.(signed_compare a b @@ modulus @@ Type.sizeof_imm t)

  let scmplt t a b = scmp t a b <  0
  let scmple t a b = scmp t a b <= 0
  let scmpgt t a b = scmp t a b >  0
  let scmpge t a b = scmp t a b >= 0

  let smin = I.signed_min
  let smax = I.signed_max

  let sless f a b =
    if f (smax a) (smin b) then I.boolean_true
    else if not (f (smin a) (smax b)) then I.boolean_false
    else I.boolean_full

  let sgreater f a b =
    if f (smin a) (smax b) then I.boolean_true
    else if not (f (smax a) (smin b)) then I.boolean_false
    else I.boolean_full

  let bool_slt t a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean @@ scmplt t a b
    | _ -> sless (scmplt t) a b

  let bool_sle t a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean @@ scmple t a b
    | _ -> sless (scmple t) a b

  let bool_sgt t a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean @@ scmpgt t a b
    | _ -> sgreater (scmpgt t) a b

  let bool_sge t a b = match I.(single_of a, single_of b) with
    | Some a, Some b -> I.boolean @@ scmpge t a b
    | _ -> sgreater (scmpge t) a b

  (* Constrain `y` to `i` in relation to the condition `x`. *)
  let constr ctx x y i = match (y : operand) with
    | `var y ->
      let i = Lazy.force i in
      Hashtbl.update ctx.cond x ~f:(function
          | Some s -> Var.Map.set s ~key:y ~data:i
          | None -> Var.Map.singleton y i)
    | _ -> ()

  (* Allow the empty interval to be created. *)
  let mkint_empty ~lo ~hi ~size =
    if Bv.(lo = hi) then I.create_empty ~size
    else I.create ~lo ~hi ~size

  let mkint = I.create_non_empty

  let lt size a b =
    (* a < b: a \in [0, umin(b)) *)
    let il = lazy begin mkint_empty ~size
        ~lo:Bv.zero
        ~hi:(I.unsigned_min b)
    end in
    (* b > a: b \in [umax(a) + 1, 0) *)
    let ir = lazy begin mkint_empty ~size
        ~lo:Bv.(succ (I.unsigned_max a) mod modulus size)
        ~hi:Bv.zero
    end in
    il, ir

  let le size a b =
    (* a <= b: a \in [0, umin(b) + 1) *)
    let il = lazy begin mkint ~size
        ~lo:Bv.zero
        ~hi:Bv.(succ (I.unsigned_min b) mod modulus size)
    end in
    (* b >= a: b \in [umax(a), 0) *)
    let ir = lazy begin mkint ~size
        ~lo:(I.unsigned_max a)
        ~hi:Bv.zero
    end in
    il, ir

  let gt size a b =
    (* a > b: a \in [umax(b) + 1, 0) *)
    let il = lazy begin mkint_empty ~size
        ~lo:Bv.(succ (I.unsigned_max b) mod modulus size)
        ~hi:Bv.zero
    end in
    (* b < a: b \in [0, umin(a)) *)
    let ir = lazy begin mkint_empty ~size
        ~lo:Bv.zero
        ~hi:(I.unsigned_min a)
    end in
    il, ir

  let ge size a b =
    (* a >= b: a \in [umax(b), 0) *)
    let il = lazy begin mkint ~size
        ~lo:(I.unsigned_max b)
        ~hi:Bv.zero
    end in
    (* b <= a: b \in [0, umin(a) + 1) *)
    let ir = lazy begin mkint ~size
        ~lo:Bv.zero
        ~hi:Bv.(succ (I.unsigned_min a) mod modulus size)
    end in
    il, ir

  let slt size a b =
    (* a <$ b: a \in [0x80..., smin(b)) *)
    let il = lazy begin mkint_empty ~size
        ~lo:(Bv.min_signed_value size)
        ~hi:(I.signed_min b)
    end in
    (* b >$ a: b \in [smax(a) + 1, 0x80...) *)
    let ir = lazy begin mkint_empty ~size
        ~lo:Bv.(succ (I.signed_max a) mod modulus size)
        ~hi:(Bv.min_signed_value size)
    end in
    il, ir

  let sle size a b =
    (* a <=$ b: a \in [0x80..., smin(b) + 1) *)
    let il = lazy begin mkint ~size
        ~lo:(Bv.min_signed_value size)
        ~hi:Bv.(succ (I.signed_min b) mod modulus size)
    end in
    (* b >=$ a: b \in [smax(a), 0x80...) *)
    let ir = lazy begin mkint ~size
        ~lo:(I.signed_max a)
        ~hi:(Bv.min_signed_value size)
    end in
    il, ir

  let sgt size a b =
    (* a >$ b: a \in [smax(b) + 1, 0x80...) *)
    let il = lazy begin mkint_empty ~size
        ~lo:Bv.(succ (I.signed_max b) mod modulus size)
        ~hi:(Bv.min_signed_value size)
    end in
    (* b <$ a: b \in [0x80..., smin(a)) *)
    let ir = lazy begin mkint_empty ~size
        ~lo:(Bv.min_signed_value size)
        ~hi:(I.signed_min a)
    end in
    il, ir

  let sge size a b =
    (* a >=$ b: a \in [smax(b), 0x80...) *)
    let il = lazy begin mkint ~size
        ~lo:(I.signed_max b)
        ~hi:(Bv.min_signed_value size)
    end in
    (* b <=$ a: b \in [0x80..., smin(a) + 1) *)
    let ir = lazy begin mkint ~size
        ~lo:(Bv.min_signed_value size)
        ~hi:Bv.(succ (I.signed_min a) mod modulus size)
    end in
    il, ir
end

let do_cmp ctx t x l r a b ~cond ~cmp =
  let il, ir = cond (Type.sizeof_imm t) a b in
  Cmp.constr ctx x l il;
  Cmp.constr ctx x r ir;
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
      ~cond:(fun _ a b -> lazy b, lazy a)
      ~cmp:Cmp.bool_eq
  | `ne (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~cond:(fun _ a b -> lazy (I.inverse b), lazy (I.inverse a))
      ~cmp:Cmp.bool_ne
  | `lt (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.lt
      ~cmp:Cmp.bool_lt
  | `le (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.le
      ~cmp:Cmp.bool_le
  | `gt (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.gt
      ~cmp:Cmp.bool_gt
  | `ge (#Type.imm as t) ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.ge
      ~cmp:Cmp.bool_ge
  | `slt t ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.slt
      ~cmp:(Cmp.bool_slt t)
  | `sle t ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.sle
      ~cmp:(Cmp.bool_sle t)
  | `sgt t ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.sgt
      ~cmp:(Cmp.bool_sgt t)
  | `sge t ->
    do_cmp ctx t x l r a b
      ~cond:Cmp.sge
      ~cmp:(Cmp.bool_sge t)
  | `eq #Type.fp
  | `ne #Type.fp
  | `lt #Type.fp
  | `le #Type.fp
  | `gt #Type.fp
  | `ge #Type.fp
  | `o _
  | `uo _ -> I.boolean_full

let interp_binop ctx o x l r a b = match (o : Insn.binop) with
  | #Insn.arith_binop as o -> interp_arith_binop o a b
  | #Insn.bitwise_binop as o -> interp_bitwise_binop o a b
  | #Insn.cmp as o -> interp_cmp ctx o x l r a b

let interp_arith_unop o a = match (o : Insn.arith_unop) with
  | `neg _ -> I.neg a

let interp_bitwise_unop o a = match (o : Insn.bitwise_unop) with
  | `clz t | `ctz t | `popcnt t -> I.create_full ~size:(Type.sizeof_imm t)
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
  | `copy _ -> Some a
  | `ref t -> Some (I.create_full ~size:(Type.sizeof_imm_base t))
  | `unref _ -> None

let interp_unop o a = match (o : Insn.unop) with
  | #Insn.arith_unop as o -> Some (interp_arith_unop o a)
  | #Insn.bitwise_unop as o -> Some (interp_bitwise_unop o a)
  | #Insn.cast as o -> Some (interp_cast o a)
  | #Insn.copy as o -> interp_copy o a

let interp_basic ctx s : Insn.basic -> state = function
  | `bop (x, o, l, r) ->
    let a = interp_operand ctx s l in
    let b = interp_operand ctx s r in
    begin match a, b with
      | None, _ | _, None -> s
      | Some a, Some b ->
        update s x @@ interp_binop ctx o x l r a b
    end
  | `uop (x, o, a) ->
    begin match interp_operand ctx s a with
      | None -> s
      | Some a ->
        interp_unop o a |>
        Option.value_map ~default:s ~f:(update s x)
    end
  | `sel (x, _, k, y, n) ->
    match interp_operand ctx s @@ `var k with
    | None -> s
    | Some c ->
      let y, n = match Hashtbl.find ctx.cond k with
        | Some s' ->
          interp_operand ctx (meet_state s s') y,
          interp_operand ctx (meet_state s @@ invert_state s') n
        | None ->
          interp_operand ctx s y,
          interp_operand ctx s n in
      match y, n with
      | None, _ | _, None -> s
      | Some y, Some n ->
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
        interp_operand ctx s o |>
        Option.value_map ~default:s ~f:(update s x))

let interp_blk ctx s b =
  let s =
    Blk.insns b |>
    Seq.fold ~init:s ~f:(interp_insn ctx) in
  match Blk.ctrl b with
  | `jmp `label (l, args) ->
    assign_blk_args ctx s l args
  | `br (c, `label (y, yargs), `label (n, nargs)) ->
    narrow ctx y c I.boolean_true;
    narrow ctx n c I.boolean_false;
    Hashtbl.find ctx.cond c |> Option.iter ~f:(fun s' ->
        Map.iteri s' ~f:(fun ~key:x ~data:i ->
            narrow ctx y x i;
            narrow ctx n x @@ I.inverse i));
    let s = assign_blk_args ctx s y yargs in
    assign_blk_args ctx s n nargs
  | `br (c, `label (y, yargs), _) ->
    narrow ctx y c I.boolean_true;
    Hashtbl.find ctx.cond c |> Option.iter ~f:(fun s' ->
        Map.iteri s' ~f:(fun ~key:x ~data:i ->
            narrow ctx y x i));
    assign_blk_args ctx s y yargs
  | `br (c, _, `label (n, nargs)) ->
    narrow ctx n c I.boolean_false;
    Hashtbl.find ctx.cond c |> Option.iter ~f:(fun s' ->
        Map.iteri s' ~f:(fun ~key:x ~data:i ->
            narrow ctx n x @@ I.inverse i));
    assign_blk_args ctx s n nargs
  | `sw (t, `var x, `label (d, args), tbl) ->
    let size = Type.sizeof_imm t in
    let s =
      (* XXX: the set of known values for `x` in each arm
         of the switch may be disjoint, so we settle for
         an overapproximation of `x` in the default case. *)
      Ctrl.Table.enum tbl |>
      Seq.fold ~init:s ~f:(fun s (v, `label (l, args)) ->
          let k = I.create_single ~value:v ~size in
          let s = assign_blk_args ctx s l args in
          (* If an arm of the switch also targets the default
             label then we shouldn't try to narrow. *)
          if Label.(l <> d) then narrow ctx l x k;
          s) in
    assign_blk_args ctx s d args
  | _ -> s

let step ctx i l _ s =
  (* Widening for block args. *)
  let s = match Label.Tree.find ctx.blks l with
    | None -> s
    | Some b ->
      (* This could be improved, but it's a start. *)
      if i > 10 then
        Blk.args b |> Seq.fold ~init:s ~f:(fun s x ->
            match sizeof x ctx with
            | Some size -> Map.set s ~key:x ~data:(I.create_full ~size)
            | None -> s)
      else s in
  (* Narrowing for constraints. *)
  match Hashtbl.find ctx.narrow l with
  | Some s' -> meet_state s' s
  | None -> s

let init_state ctx fn =
  let init =
    Func.args fn |>
    Seq.filter_map ~f:(fun (x, t) -> match t with
        | #Type.basic -> Some x
        | `name _ -> None) |>
    Seq.fold ~init:empty_state ~f:(fun s x ->
        match sizeof x ctx with
        | Some size -> Map.set s ~key:x ~data:(I.create_full ~size)
        | None -> s) in
  let init =
    Func.slots fn |> Seq.fold ~init ~f:(fun s x ->
        let data = I.create_full ~size:(Type.sizeof_imm_base ctx.word) in
        Map.set s ~key:(Func.Slot.var x) ~data) in
  Solution.create Label.(Map.singleton pseudoentry init) empty_state

let transfer ctx l s = match Label.Tree.find ctx.blks l with
  | Some b -> interp_blk ctx s b
  | None -> s

type t = {
  insns : state Label.Table.t;
  input : (Label.t, state) Solution.t;
}

let insn t = Hashtbl.find t.insns
let input t = t.input

let analyze ?steps fn ~word ~typeof =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let ctx = create_ctx ~blks ~word ~typeof in
    let input = Graphlib.fixpoint (module Cfg) cfg ?steps
        ~step:(step ctx)
        ~init:(init_state ctx fn)
        ~equal:equal_state
        ~merge:join_state
        ~f:(transfer ctx) in
    {insns = ctx.insns; input}
  else
    invalid_argf
      "Intervals analysis: function $%s is not in SSA form"
      (Func.name fn) ()
