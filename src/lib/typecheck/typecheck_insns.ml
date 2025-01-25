(* Checking individual instructions of a block. *)

open Core
open Virtual
open Typecheck_common

let expect_ptr_size_base_var v t word msg =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Expected imm_base of type %a for var %a in %s %a \
           in block %a in function $%s, got %a"
    Type.pp_imm_base word Var.pp v msg Label.pp
    l Label.pp (Blk.label blk) (Func.name fn)
    Type.pp t ()

let expect_ptr_size_alist v t word msg =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Expected imm_base of type %a for alist %a in %s %a \
           in block %a in function $%s, got %a"
    Type.pp_imm_base word Insn.pp_alist v msg Label.pp l
    Label.pp (Blk.label blk) (Func.name fn) Type.pp t ()

let expect_ptr_size_var v t msg =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Expected imm_base type for var %a in %s %a in \
           block %a in function $%s, got %a"
    Var.pp v msg Label.pp l Label.pp (Blk.label blk)
    (Func.name fn) Type.pp t ()

let unify_fail_arg t a t' =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Expected type %a for arg %a in instruction %a in \
           block %a in function $%s, got %a"
    Type.pp t pp_operand a Label.pp l Label.pp
    (Blk.label blk) (Func.name fn) Type.pp t' ()

let unify_arg ta a t = match ta, t with
  | #Type.t as ta, _ ->
    let t = (t :> Type.t) in
    M.unless Type.(ta = t) @@ fun () -> unify_fail_arg t a ta

type binop_typ = [
  | Type.basic
  | `flag
]

let op_arith_binop tl al tr ar (o : Insn.arith_binop) =
  let t = match o with
    | `add t
    | `div t
    | `mul t
    | `sub t -> t
    | `rem t
    | `mulh t
    | `udiv t
    | `umulh t
    | `urem t -> (t :> Type.basic) in
  let* () = unify_arg tl al t in
  let+ () = unify_arg tr ar t in
  (t :> binop_typ)

let op_bitwise_binop tl al tr ar (o : Insn.bitwise_binop) =
  let t = match o with
    | `and_ t
    | `or_ t
    | `asr_ t
    | `lsl_ t
    | `lsr_ t
    | `rol t
    | `ror t
    | `xor t -> t in
  let* () = unify_arg tl al t in
  let+ () = unify_arg tr ar t in
  (t :> binop_typ)

let op_cmp tl al tr ar (o : Insn.cmp) =
  let t = match o with
    | `eq t
    | `ge t
    | `gt t
    | `le t
    | `lt t
    |` ne t -> t
    | `o t
    | `uo t -> (t :> Type.basic)
    | `sge t
    | `sgt t
    | `sle t
    | `slt t -> (t :> Type.basic) in
  let* () = unify_arg tl al t in
  let+ () = unify_arg tr ar t in
  `flag

let op_arith_unop ta a (o : Insn.arith_unop) =
  let t = match o with
    | `neg t -> t in
  let+ () = unify_arg ta a t in
  t

let op_bitwise_unop ta a (o : Insn.bitwise_unop) =
  let t = match o with
    | `clz t
    | `ctz t
    | `not_ t
    | `popcnt t -> t in
  let+ () = unify_arg ta a t in
  (t :> Type.basic)

let unify_fp_fail t a =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Expected floating point type for arg %a in instruction %a \
           in block %a in function $%s, got %a"
    pp_operand a Label.pp l Label.pp (Blk.label blk)
    (Func.name fn) Type.pp t ()

let unify_imm_fail t a =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Expected immediate type for arg %a in instruction %a \
           in block %a in function $%s, got %a"
    pp_operand a Label.pp l Label.pp (Blk.label blk)
    (Func.name fn) Type.pp t ()

let unify_flag_fail t v =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Expected flag type for var %a in instruction %a \
           in block %a in function $%s, got %a"
    Var.pp v Label.pp l Label.pp (Blk.label blk)
    (Func.name fn) Type.pp t ()

let unify_fext_fail t a =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Invalid floating point type %a for arg %a in instruction \
           %a in block %a in function $%s"
    Type.pp t pp_operand a Label.pp l Label.pp
    (Blk.label blk) (Func.name fn) ()

let unify_bits_fail op t ta a =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Invalid type for arg %a in instruction %a in block %a in \
           function $%s: '%s' cannot convert %a to %a"
    pp_operand a Label.pp l Label.pp (Blk.label blk) (Func.name fn)
    op Type.pp ta Type.pp (t :> Type.t) ()

let op_cast ta a : Insn.cast -> Type.basic t = function
  | `fext t ->
    begin match ta with
      | #Type.fp as f when Type.sizeof_fp t >= Type.sizeof_fp f ->
        !!(t :> Type.basic)
      | #Type.fp -> unify_fext_fail ta a
      | _ -> unify_imm_fail ta a
    end
  | `fibits t ->
    begin match t, ta with
      | (`f32, `i32) | (`f64, `i64) -> !!(t :> Type.basic)
      | _ -> unify_bits_fail "fibits" t ta a
    end
  | `flag t ->
    begin match ta with
      | `flag -> !!(t :> Type.basic)
      | _ -> unify_bits_fail "flag" t ta a
    end
  | `ftosi (tf, ti)
  | `ftoui (tf, ti) ->
    let+ () = unify_arg ta a (tf :> Type.t) in
    (ti :> Type.basic)
  | `ftrunc t ->
    begin match ta with
      | #Type.fp as f when Type.sizeof_fp t <= Type.sizeof_fp f ->
        !!(t :> Type.basic)
      | #Type.fp -> unify_fext_fail ta a
      | _ -> unify_fp_fail ta a
    end
  | `ifbits t ->
    begin match t, ta with
      | (`i32, `f32) | (`i64, `f64) -> !!(t :> Type.basic)
      | _ -> unify_bits_fail "ifbits" t ta a
    end
  | `itrunc t ->
    begin match ta with
      | #Type.imm as i when Type.sizeof_imm t <= Type.sizeof_imm i ->
        !!(t :> Type.basic)
      | #Type.imm -> unify_fext_fail ta a
      | _ -> unify_imm_fail ta a
    end
  | `sext t | `zext t ->
    begin match ta with
      | #Type.imm as i when Type.sizeof_imm t >= Type.sizeof_imm i ->
        !!(t :> Type.basic)
      | #Type.imm -> unify_fext_fail ta a
      | _ -> unify_imm_fail ta a
    end
  | `sitof (ti, tf)
  | `uitof (ti, tf) ->
    let+ () = unify_arg ta a (ti :> Type.t) in
    (tf :> Type.basic)

let op_copy ta a : Insn.copy -> Type.t t = function
  | `copy t ->
    begin match ta, t with
      | #Type.basic as b, t when Type.equal_basic b t -> !!(t :> Type.t)
      | _ -> unify_fail_arg (t :> Type.t) a ta
    end

let op_binop env v b al ar =
  let* fn = getfn in
  let* tl = typeof_arg fn env al in
  let* tr = typeof_arg fn env ar in
  let* t = match b with
    | #Insn.arith_binop as o ->
      op_arith_binop tl al tr ar o
    | #Insn.bitwise_binop as o ->
      op_bitwise_binop tl al tr ar o
    | #Insn.cmp as o ->
      op_cmp tl al tr ar o in
  M.lift_err @@ Env.add_var fn v (t :> Type.t) env

let op_unop env v u a =
  let* fn = getfn in
  let* ta = typeof_arg fn env a in
  let* t = match u with
    | #Insn.arith_unop as o ->
      let+ t = op_arith_unop ta a o in
      (t :> Type.t)
    | #Insn.bitwise_unop as o ->
      let+ t = op_bitwise_unop ta a o in
      (t :> Type.t)
    | #Insn.cast as o ->
      let+ t = op_cast ta a o in
      (t :> Type.t)
    | #Insn.copy as o ->
      op_copy ta a o in
  M.lift_err @@ Env.add_var fn v (t :> Type.t) env

let op_mem_load env word x t a =
  let* t = typeof_type_arg env t in
  let* fn = getfn in
  let* ta = typeof_arg fn env a in
  let* () = unify_arg ta a (word :> Type.t) in
  M.lift_err @@ Env.add_var fn x (t :> Type.t) env

let op_mem_store env word t v a =
  let* t = typeof_type_arg env t in
  let* fn = getfn in
  let* tv = typeof_arg fn env v in
  let* ta = typeof_arg fn env a in
  let* () = unify_arg tv v (t :> Type.t) in
  let+ () = unify_arg ta a (word :> Type.t) in
  env

let op_mem env m =
  let* word = target >>| Target.word in
  match m with
  | `load (x, t, a) -> op_mem_load env word x t a
  | `store (t, v, a) -> op_mem_store env word t v a

let op_sel env v t c al ar =
  let* fn = getfn in
  let*? tc = Env.typeof_var fn c env in
  let* () = match tc with
    | `flag -> !!()
    | _ -> unify_flag_fail tc c in
  let* tl = typeof_arg fn env al in
  let* tr = typeof_arg fn env ar in
  let* () = unify_arg tl al (t :> Type.t) in
  let* () = unify_arg tr ar (t :> Type.t) in
  M.lift_err @@ Env.add_var fn v (t :> Type.t) env

let op_basic env : Insn.basic -> env t = function
  | `bop (v, b, al, ar) -> op_binop env v b al ar
  | `uop (v, u, a) -> op_unop env v u a
  | `sel (v, t, c, al, ar) -> op_sel env v t c al ar

let unify_fail_void_call t s =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Failed to unify return types %a and <void> for call \
           at %a to function $%s in block %a of function $%s"
    Type.pp_ret t Label.pp l s Label.pp (Blk.label blk) (Func.name fn) ()

let unify_fail_call_ret t1 t2 s =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Failed to unify return types %a and %a for call at %a \
           to function $%s in block %a of function $%s"
    Type.pp_ret t1 Type.pp_ret t2 Label.pp l s Label.pp
    (Blk.label blk) (Func.name fn) ()

let non_variadic_call s =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Variadic call at %a to non-variadic function $%s in \
           block %a of function $%s"
    Label.pp l s Label.pp (Blk.label blk) (Func.name fn) ()

let unequal_lengths_call s args targs =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Call at %a to function $%s in block %a of function $%s: \
           expected %d arguments, got %d"
    Label.pp l s Label.pp (Blk.label blk) (Func.name fn)
    (List.length targs) (List.length args) ()

let unify_fail_call_arg s t a t' =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Call at %a to function $%s in block %a of function $%s: \
           expected %a for arg %a, got %a"
    Label.pp l s Label.pp (Blk.label blk) (Func.name fn)
    Type.pp t pp_operand a Type.pp t' ()

let name_arg_fail s cn n a =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Call at %a to function $%s in block %a of function $%s: \
           expected compound type :%s, got :%s for arg %a"
    Label.pp l s Label.pp (Blk.label blk) (Func.name fn)
    cn n pp_operand a ()

let expected_compound_arg s cn t a =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Call at %a to function $%s in block %a of function $%s: \
           expected compound type :%s, got %a for arg %a"
    Label.pp l s Label.pp (Blk.label blk) (Func.name fn)
    cn Type.pp t pp_operand a ()

let expected_basic_arg s cn t a =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "Call at %a to function $%s in block %a of function $%s: \
           expected type %a, got :%s for arg %a"
    Label.pp l s Label.pp (Blk.label blk) (Func.name fn)
    Type.pp t cn pp_operand a ()

let check_call_var env v =
  let* fn = getfn in
  let*? t = Env.typeof_var fn v env in
  let* word = target >>| Target.word in
  (* No guarantees for indirect call, just make sure that
     the var is pointer-sized. *)
  match t with
  | #Type.imm_base as b ->
    M.unless (Type.equal_imm_base b word) @@ fun () ->
    expect_ptr_size_base_var v t word "call"
  | _ -> expect_ptr_size_var v t "call"

let check_call_sym_ret t ret s = match t, ret with
  | None, Some t -> unify_fail_void_call (t :> Type.ret) s
  | Some t, None -> unify_fail_void_call t s
  | Some t1, Some t2 when Type.equal_ret t1 (t2 :> Type.ret) -> !!()
  | Some t1, Some t2 -> unify_fail_call_ret t1 (t2 :> Type.ret) s
  | None, None -> !!()

let check_call_sym_variadic s vargs variadic =
  M.unless (variadic || List.is_empty vargs) @@ fun () ->
  non_variadic_call s

let check_call_sym_args env s (args : (operand * Type.arg) list) =
  let* fn = getfn in
  M.List.iter args ~f:(fun (a, t) ->
      let* at = typeof_arg fn env a in
      match at, t with
      | (#Type.compound as c), `name n ->
        let cn = Type.compound_name c in
        if String.(cn = n) then !!()
        else name_arg_fail s cn n a
      | (#Type.compound as c), (#Type.basic as b) ->
        let cn = Type.compound_name c in
        expected_compound_arg s cn (b : Type.t) a
      | (#Type.t as at), `name n ->
        expected_basic_arg s n at a
      | (#Type.t as at), (#Type.basic as t) ->
        (* Normal unification. *)
        let t = (t :> Type.t) in
        if Type.(at = t) then !!()
        else unify_fail_call_arg s t a at)

let check_call_sym env t args vargs s ret targs variadic =
  let* () = check_call_sym_ret t ret s in
  let* () = check_call_sym_variadic s vargs variadic in
  match List.zip args targs with
  | Unequal_lengths -> unequal_lengths_call s args targs
  | Ok z -> check_call_sym_args env s z

let check_call env t args vargs : global -> unit t = function
  | `addr _ -> !!() (* No guarantees for call to raw address. *)
  | `var v -> check_call_var env v
  | `sym (s, 0) ->
    begin match Env.typeof_fn s env with
      | Some (`proto (ret, targs, variadic)) ->
        check_call_sym env t args vargs s ret targs variadic
      | None -> !!() (* No guarantees for an external function. *)
    end
  | `sym _ -> !!() (* No guarantees for a symbol with a non-zero offset. *)

let op_call env : Insn.call -> env t = function
  | `call (Some (v, t), g, args, vargs) ->
    let* () =
      let t = Some (t :> Type.ret) in
      check_call env t args vargs g in
    let* fn = getfn in
    let* t = typeof_type_ret env t in
    M.lift_err @@ Env.add_var fn v t env
  | `call (None, g, args, vargs) ->
    let+ () = check_call env None args vargs g in
    env

let variadic_check_list_ty v t word = match t with
  | #Type.imm_base as b ->
    (* Argument is expected to be a pointer. *)
    if Type.equal_imm_base b word then !!()
    else expect_ptr_size_alist v t word "variadic instruction"
  | _ -> expect_ptr_size_alist v t word "variadic instruction"

let variadic_in_fixed_args =
  let* fn = getfn and* blk = getblk and* l = getins in
  M.failf "In function %s, block %a, instruction %a, attempted to use a \
           variadic instruction in a function with fixed arguments."
    (Func.name fn) Label.pp (Blk.label blk) Label.pp l ()

let op_variadic env (v : Insn.variadic) =
  let* fn = getfn in
  let* () = M.unless (Func.variadic fn) @@ fun () ->
    variadic_in_fixed_args in
  let* word = target >>| Target.word in
  match v with
  | `vaarg (x, t, y) ->
    let*? ty = match y with
      | `var y -> Env.typeof_var fn y env
      | `addr _ | `sym _ -> Ok (word :> Type.t) in
    let* () = variadic_check_list_ty y ty word in
    let* t = typeof_type_arg env t in
    M.lift_err @@ Env.add_var fn x t env
  | `vastart v ->
    let*? t = match v with
      | `var v -> Env.typeof_var fn v env
      | `addr _ | `sym _ -> Ok (word :> Type.t) in
    let+ () = variadic_check_list_ty v t word in
    env

let op env : Insn.op -> env t = function
  | #Insn.basic    as b -> op_basic    env b
  | #Insn.call     as c -> op_call     env c
  | #Insn.mem      as m -> op_mem      env m
  | #Insn.variadic as v -> op_variadic env v

let go seen =
  let* init = getenv and* blk = getblk in
  let* env = Blk.insns blk |> M.Seq.fold ~init ~f:(fun env d ->
      let l = Insn.label d in
      let* () = M.update @@ fun ctx -> {ctx with ins = Some l} in
      let o = Insn.op d in
      let* () = match Hash_set.strict_add seen l with
        | Ok () -> !!()
        | Error _ ->
          let* fn = getfn in
          M.failf "Instruction for label %a in block %a already \
                   exists in function $%s"
            Label.pp l Label.pp (Blk.label blk) (Func.name fn) () in
      op env o) in
  updenv env
