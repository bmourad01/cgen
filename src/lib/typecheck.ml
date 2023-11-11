open Core
open Regular.Std
open Graphlib.Std
open Virtual

let unify_fail t t' v fn = Or_error.errorf
    "Failed to unify types '%a' and '%a' for var %a in function $%s"
    Type.pps t Type.pps t' Var.pps v @@ Func.name fn

(* Typing environment. *)

module Env = struct
  type t = {
    target : Target.t;
    denv   : Type.compound String.Map.t;
    fenv   : Type.proto String.Map.t;
    tenv   : Type.compound String.Map.t;
    venv   : Type.t Var.Map.t String.Map.t;
    genv   : Type.layout String.Map.t;
  }

  let create target = {
    target;
    denv = String.Map.empty;
    fenv = String.Map.empty;
    tenv = String.Map.empty;
    venv = String.Map.empty;
    genv = String.Map.empty;
  }

  let target t = t.target

  let add_data d env =
    let name = Data.name d in
    match Map.add env.denv ~key:name ~data:(Data.typeof d env.target) with
    | `Duplicate -> Or_error.errorf "Redefinition of data $%s" name
    | `Ok denv -> Ok {env with denv}

  (* If we don't have the data defined in the module, then assume it is
     external (i.e. it is linked with our program a posteriori), and that
     the user accepts the risk. *)
  let typeof_data name env = Map.find env.denv name

  let add_fn fn env =
    let name = Func.name fn in
    match Map.add env.fenv ~key:name ~data:(Func.typeof fn) with
    | `Duplicate -> Or_error.errorf "Redefinition of function $%s" name
    | `Ok fenv -> Ok {env with fenv}

  (* If we don't have the function defined in the module, then assume
     it is external (i.e. it is linked with our program a posteriori),
     and that the user accepts the risk. *)
  let typeof_fn name env = Map.find env.fenv name

  let check_typ_align t name = match Type.compound_align t with
    | Some n when n < 1 || (n land (n - 1)) <> 0 ->
      Or_error.errorf "Invalid alignment %d of type :%s, must be \
                       positive power of 2" n name
    | Some _ | None -> Ok ()

  let add_typ t env =
    let name = Type.compound_name t in
    check_typ_align t name |> Or_error.bind ~f:(fun () ->
        match Map.add env.tenv ~key:name ~data:t with
        | `Duplicate -> Or_error.errorf "Redefinition of type :%s" name
        | `Ok tenv -> Ok {env with tenv})

  let typeof_typ name env = match Map.find env.tenv name with
    | None -> Or_error.errorf "Undefined type %s" name
    | Some t -> Ok t

  let typeof_var fn v env =
    let fname = Func.name fn in
    match Map.find env.venv fname with
    | None ->
      Or_error.errorf
        "No function $%s in environment for variable %a"
        fname Var.pps v
    | Some m -> match Map.find m @@ Var.base v with
      | Some t -> Ok t
      | None ->
        Or_error.errorf
          "No variable %a in function $%s"
          Var.pps v fname

  exception Unify_fail of Type.t

  let add_var fn v t env = try
      let v = Var.base v in
      let venv = Map.update env.venv (Func.name fn) ~f:(function
          | None -> Var.Map.singleton v t
          | Some m -> Map.update m v ~f:(function
              | Some t' when Type.(t <> t') -> raise @@ Unify_fail t'
              | Some _ -> t
              | None -> t)) in
      Ok {env with venv}
    with Unify_fail t' -> unify_fail t t' v fn

  let layout name env = match Map.find env.genv name with
    | None -> Or_error.errorf "Type :%s not found in gamma" name
    | Some l -> Ok l
end

type env = Env.t

type ctx = {
  env : env;
  fn  : func option;
  blk : blk option;
  ins : Label.t option;
}

module M = Sm.Make(struct
    type state = ctx
    let error_prefix = "Type error"
  end)

include M.Syntax

type 'a t = 'a M.m

(* Helper functions. *)

let getenv = M.gets @@ fun ctx -> ctx.env

let getfn = M.gets @@ fun ctx -> match ctx.fn with
  | None -> assert false
  | Some fn -> fn

let getblk = M.gets @@ fun ctx -> match ctx.blk with
  | None -> assert false
  | Some blk -> blk

let getins = M.gets @@ fun ctx -> match ctx.ins with
  | None -> assert false
  | Some ins -> ins

let target =
  let+ env = getenv in
  env.target

let updenv env = M.update @@ fun ctx -> {ctx with env}

let max_i8  = Bv.of_string "0xff"
let max_i16 = Bv.of_string "0xffff"
let max_i32 = Bv.of_string "0xffffffff"
let max_i64 = Bv.of_string "0xffffffffffffffff"

let max_of_imm : Type.imm -> Bv.t = function
  | `i8  -> max_i8
  | `i16 -> max_i16
  | `i32 -> max_i32
  | `i64 -> max_i64

let check_max i t =
  let m = max_of_imm t in
  if Bv.(i > m) then
    M.failf "Integer %a does not fit in type %a"
      Bv.pp i Type.pp_imm t ()
  else !!(t :> Type.t)

let typeof_const : const -> Type.t t = function
  | `bool _ -> !!`flag
  | `int (i, t) -> check_max i t
  | `float _ -> !!`f32
  | `double _ -> !!`f64
  | `sym _ ->
    let+ t = target in
    (Target.word t :> Type.t)

let typeof_arg fn env : operand -> Type.t t = function
  | #const as c -> typeof_const c
  | `var v -> M.lift_err @@ Env.typeof_var fn v env

let typeof_type_arg env : Type.arg -> Type.t t = function
  | #Type.basic as t -> !!(t :> Type.t)
  | `name n ->
    let*? t = Env.typeof_typ n env in
    !!(t :> Type.t)

(* Checking individual instructions of a block. *)

module Insns = struct
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
      if Type.(ta = t) then !!() else unify_fail_arg t a ta

  type binop_typ = [
    | Type.basic
    | `flag
  ]

  let op_arith_binop tl al tr ar (o : Insn.arith_binop) =
    let t = match o with
      | `add t
      | `div t
      | `mul t
      | `rem t
      | `sub t -> t
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

  let ref_expected_compound t a =
    let* fn = getfn and* blk = getblk and* l = getins in
    M.failf "Expected compound type for arg %a in 'ref' instruction \
             %a in block %a in function $%s, got %a"
      pp_operand a Label.pp l Label.pp (Blk.label blk)
      (Func.name fn) Type.pp (t :> Type.t) ()

  let unref_expected_word_size t w =
    let* fn = getfn and* blk = getblk and* l = getins in
    M.failf "Expected type %a for 'unref' instruction %a in block %a \
             in function $%s, got %a"
      Type.pp (w :> Type.t) Label.pp l Label.pp (Blk.label blk)
      (Func.name fn) Type.pp (t :> Type.t) ()

  let op_copy ta a : Insn.copy -> Type.t t = function
    | `copy t ->
      begin match ta, t with
        | #Type.basic as b, t when Type.equal_basic b t -> !!(t :> Type.t)
        | _ -> unify_fail_arg (t :> Type.t) a ta
      end
    | `ref ->
      let* w = target >>| Target.word in
      begin match ta with
        | #Type.compound -> !!(w :> Type.t)
        | _ -> ref_expected_compound ta a
      end
    | `unref s ->
      let* env = getenv in
      let*? t = Env.typeof_typ s env in
      let w = Target.word @@ Env.target env in
      if Type.equal ta (w :> Type.t) then !!(t :> Type.t)
      else unref_expected_word_size ta w

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
    let* fn = getfn in
    let* ta = typeof_arg fn env a in
    let* () = unify_arg ta a (word :> Type.t) in
    M.lift_err @@ Env.add_var fn x (t :> Type.t) env

  let op_mem_store env word t v a =
    let* fn = getfn in
    let* tv = typeof_arg fn env v in
    let* ta = typeof_arg fn env a in
    let* () = unify_arg tv a (t :> Type.t) in
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
      Type.pp_arg t Label.pp l s Label.pp (Blk.label blk) (Func.name fn) ()

  let unify_fail_call_ret t1 t2 s =
    let* fn = getfn and* blk = getblk and* l = getins in
    M.failf "Failed to unify return types %a and %a for call at %a \
             to function $%s in block %a of function $%s"
      Type.pp_arg t1 Type.pp_arg t2 Label.pp l s Label.pp
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
      if Type.equal_imm_base b word then !!()
      else expect_ptr_size_base_var v t word "call"
    | _ -> expect_ptr_size_var v t "call"

  let check_call_sym_ret t ret s = match t, ret with
    | None, Some t -> unify_fail_void_call (t :> Type.arg) s
    | Some t, None -> unify_fail_void_call t s
    | Some t1, Some t2 when Type.equal_arg t1 (t2 :> Type.arg) -> !!()
    | Some t1, Some t2 -> unify_fail_call_ret t1 (t2 :> Type.arg) s
    | None, None -> !!()

  let check_call_sym_variadic s vargs variadic =
    if variadic || List.is_empty vargs then !!()
    else non_variadic_call s

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
        let t = Some (t :> Type.arg) in
        check_call env t args vargs g in
      let* fn = getfn in
      let* t = typeof_type_arg env t in
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
    let* () = if Func.variadic fn then !!()
      else variadic_in_fixed_args in
    let* word = target >>| Target.word in
    match v with
    | `vaarg (x, t, y) ->
      let*? ty = match y with
        | `var y -> Env.typeof_var fn y env
        | `addr _ | `sym _ -> Ok (word :> Type.t) in
      let* () = variadic_check_list_ty y ty word in
      M.lift_err @@ Env.add_var fn x (t :> Type.t) env
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
end

(* Checking control-flow instructions of a block. *)

module Ctrls = struct
  let unequal_lengths_ctrl l args targs =
    let* fn = getfn and* blk = getblk in
    M.failf "Jump to %a in block %a of function $%s: \
             expected %d arguments, got %d"
      Label.pp l Label.pp (Blk.label blk) (Func.name fn)
      (List.length targs) (List.length args) ()

  let check_var_dst v =
    let* env = getenv and* fn = getfn in
    let word = Target.word @@ Env.target env in
    let*? t = Env.typeof_var fn v env in
    if Type.(t = (word :> Type.t)) then !!()
    else M.lift_err @@ unify_fail t (word :> Type.t) v fn

  let check_label_dst blks l args =
    let* fn = getfn and* blk = getblk in
    let* b = match Label.Tree.find blks l with
      | Some b -> !!b
      | None ->
        M.failf "Jump destination %a at block %a in function $%s \
                 does not exist."
          Label.pp l Label.pp (Blk.label blk) (Func.name fn) () in
    let targs = Seq.to_list @@ Blk.args b in
    match List.zip args targs with
    | Unequal_lengths -> unequal_lengths_ctrl l args targs
    | Ok z -> M.List.iter z ~f:(fun (a, x) ->
        let* env = getenv in
        let* ta = typeof_arg fn env a in
        let*? env = Env.add_var fn x ta env in
        updenv env)

  let check_dst blks : dst -> unit t = function
    | `addr _ | `sym _ -> !!()
    | `var v -> check_var_dst v
    | `label (l, args) -> check_label_dst blks l args

  let unify_flag_fail_ctrl t v =
    let* fn = getfn and* blk = getblk in
    M.failf "Expected mem type for var %a of jnz in block %a in \
             function $%s, got %a"
      Var.pp v Label.pp (Blk.label blk) (Func.name fn) Type.pp t ()

  let unify_fail_void_ret t =
    let* fn = getfn and* blk = getblk in
    M.failf "Failed to unify return types %a and <void> for \
             ret in block %a of function $%s"
      Type.pp t Label.pp (Blk.label blk) (Func.name fn) ()

  let unify_fail_ret t1 t2 =
    let* fn = getfn and* blk = getblk in
    M.failf "Failed to unify return types %a and %a for \
             ret in block %a of function $%s"
      Type.pp t1 Type.pp t2 Label.pp (Blk.label blk) (Func.name fn) ()

  let ctrl_br blks c t f =
    let* env = getenv and* fn = getfn in
    let*? tc = Env.typeof_var fn c env in
    let* () = match tc with
      | `flag -> !!()
      | _ -> unify_flag_fail_ctrl tc c in
    let* () = check_dst blks t in
    check_dst blks f

  let ctrl_ret_none =
    let* env = getenv and* fn = getfn in
    match Func.return fn with
    | Some t -> typeof_type_arg env t >>= unify_fail_void_ret
    | None -> !!()

  let ctrl_ret_some r =
    let* env = getenv and* fn = getfn in
    let* tr = typeof_arg fn env r in
    match tr, Func.return fn with
    | t, None -> unify_fail_void_ret t
    | #Type.t as r, Some t ->
      let* t' = typeof_type_arg env t in
      if Type.(r = t') then !!()
      else unify_fail_ret r t'

  let sw_unify_fail t t' =
    let* fn = getfn and* blk = getblk in
    M.failf "Expected type %a for index of `sw` instruction in \
             block %a in function $%s, got %a"
      Type.pp t Label.pp (Blk.label blk)
      (Func.name fn) Type.pp t' ()

  let check_sw_index t i =
    let m = max_of_imm t in
    if Bv.(i > m) then
      let* fn = getfn and* blk = getblk in
      M.failf "In `sw.%a` instruction in block %a in function $%s: \
               index %a_%a does not fit in type %a"
        Type.pp_imm t Label.pp (Blk.label blk) (Func.name fn)
        Bv.pp i Type.pp_imm t Type.pp_imm t ()
    else !!()

  let ctrl_sw blks t v d tbl =
    let t' = (t :> Type.t) in
    let* env = getenv and* fn = getfn in
    let*? tv = match v with
      | `var v -> Env.typeof_var fn v env
      | `sym _ -> Ok (Target.word env.target :> Type.t) in
    if Type.(t' = tv) then
      let* () = check_dst blks (d :> dst) in
      Ctrl.Table.enum tbl |> M.Seq.iter ~f:(fun (i, l) ->
          let* () = check_sw_index t i in
          check_dst blks (l :> dst))
    else sw_unify_fail t' tv

  let unify_fail_void_tcall t f =
    let* fn = getfn and* blk = getblk in
    M.failf "Failed to unify return types %a and <void> for \
             tail call to %s in block %a of function $%s"
      Type.pp_arg t (Format.asprintf "%a" pp_global f)
      Label.pp (Blk.label blk) (Func.name fn) ()

  let unify_fail_tcall_ret t1 t2 f =
    let* fn = getfn and* blk = getblk in
    M.failf "Failed to unify return types %a and %a for \
             tail call to %a in block %a of function $%s"
      Type.pp_arg t1 Type.pp_arg t2 pp_global f
      Label.pp (Blk.label blk) (Func.name fn) ()

  let ctrl_tcall t f args vargs =
    let* env = getenv in
    let t = Option.map t ~f:(fun t -> (t :> Type.arg)) in
    let* tf = getfn >>| Func.typeof in
    let* () = match tf, t with
      | `proto (Some rt, _, _), Some t ->
        let ta = (rt :> Type.arg) in
        if Type.equal_arg ta t then !!()
        else unify_fail_tcall_ret ta t f
      | `proto (Some t, _, _), None ->
        unify_fail_void_tcall (t :> Type.arg) f
      | `proto (None, _, _), (None | Some _) -> !!() in
    Insns.check_call env t args vargs f

  let go blks c =
    (* A bit of a hack, but it's a convention that the control
       instruction's label is represented by the block it
       belongs to. *)
    let* () = M.update @@ fun ctx -> match ctx.blk with
      | Some b -> {ctx with ins = Some (Blk.label b)}
      | None -> assert false in
    match c with
    | `hlt -> !!()
    | `jmp d -> check_dst blks d
    | `br (c, t, f) -> ctrl_br blks c t f
    | `ret None -> ctrl_ret_none
    | `ret (Some r) -> ctrl_ret_some r
    | `sw (t, v, d, tbl) -> ctrl_sw blks t v d tbl
    | `tcall (t, f, args, vargs) -> ctrl_tcall t f args vargs
end

(* Checking function definitions. *)

module Funcs = struct
  let not_pseudo = Fn.non Label.is_pseudo

  let blk_args =
    let* fn = getfn and* blk = getblk and* env = getenv in
    let* env, _ =
      let init = env, Var.Set.empty in
      Blk.args blk |> M.Seq.fold ~init ~f:(fun (env, seen) x ->
          if Set.mem seen x then
            M.failf "Duplicate argument %a for block %a in function $%s"
              Var.pp x Label.pp (Blk.label blk) (Func.name fn) ()
          else
            let*? _ = Env.typeof_var fn x env in
            !!(env, Set.add seen x)) in
    updenv env

  let rec check_blk doms rpo blks seen l =
    let* blk = match Label.Tree.find blks l with
      | Some blk -> !!blk
      | None ->
        let* fn = getfn in
        M.failf "Invariant broken in function $%s: block %a is missing"
          (Func.name fn) Label.pp l () in
    let* () = M.update @@ fun ctx -> {ctx with blk = Some blk} in
    let* () = blk_args in
    let* () = Insns.go seen in
    let* () = Ctrls.go blks @@ Blk.ctrl blk in
    let rpn = Hashtbl.find_exn rpo in
    Tree.children doms l |> Seq.filter ~f:not_pseudo |> Seq.to_list |>
    List.sort ~compare:(fun a b -> compare (rpn a) (rpn b)) |>
    M.List.iter ~f:(check_blk doms rpo blks seen)

  let make_rpo cfg start =
    let rpo = Label.Table.create () in
    Graphlib.reverse_postorder_traverse (module Cfg) cfg ~start |>
    Seq.iteri ~f:(fun i l -> Hashtbl.set rpo ~key:l ~data:i);
    rpo

  let typ_of_typ_arg env = function
    | #Type.basic as b -> Ok (b :> Type.t)
    | `name n ->
      Env.typeof_typ n env |>
      Or_error.map ~f:(fun t -> (t :> Type.t))

  let args =
    let* env = getenv and* fn = getfn in
    let* env, _ =
      let init = env, Var.Set.empty in
      Func.args fn |> M.Seq.fold ~init ~f:(fun (env, seen) (x, t) ->
          if Set.mem seen x then
            M.failf "Duplicate argument %a for function $%s"
              Var.pp x (Func.name fn) ()
          else
            let*? t = typ_of_typ_arg env t in
            let*? env = Env.add_var fn x t env in
            !!(env, Set.add seen x)) in
    updenv env

  let slots =
    let* env = getenv and* fn = getfn in
    let t = (Target.word (Env.target env) :> Type.t) in
    let* env, _ =
      let init = env, Var.Set.empty in
      Func.slots fn |> M.Seq.fold ~init ~f:(fun (env, seen) s ->
          let x = Func.Slot.var s in
          if Set.mem seen x then
            M.failf "Duplicate slot %a in function $%s"
              Var.pp x (Func.name fn) ()
          else
            let*? env = Env.add_var fn x t env in
            !!(env, Set.add seen x)) in
    updenv env

  let check_entry_inc fn cfg =
    let l = Func.entry fn in
    Cfg.Node.preds l cfg |>
    Seq.filter ~f:(Fn.non Label.is_pseudo) |>
    Seq.length |> function
    | n when n > 0 ->
      M.failf "Entry block %a of function $%s contains %d \
               incoming edges, expected 0"
        Label.pp l (Func.name fn) n ()
    | _ -> !!()

  let add m =
    let* init = getenv in
    let* env = Module.funs m |> M.Seq.fold ~init ~f:(fun env fn ->
        M.lift_err @@ Env.add_fn fn env) in
    updenv env

  let check fn =
    let* () = M.update @@ fun ctx -> {ctx with fn = Some fn} in
    let* () = args in
    let* () = slots in
    (* Be aware of duplicate labels for instructions. *)
    let seen = Label.Hash_set.create () in
    let*? blks = try Ok (Func.map_of_blks fn) with
      | Invalid_argument msg -> Or_error.error_string msg in
    let cfg = Cfg.create fn in
    let* () = check_entry_inc fn cfg in
    let start = Label.pseudoentry in
    (* We will traverse the blocks according to the dominator tree
       so that we get the right ordering for definitions. *)
    let doms = Graphlib.dominators (module Cfg) cfg start in
    (* However, it requires us to visit children of each node in
       the tree according to the reverse postorder traversal. *)
    check_blk doms (make_rpo cfg start) blks seen @@ Func.entry fn
end

(* Checking global data. *)

module Datas = struct
  let invalid_elt d elt msg =
    M.failf "Invalid element %a ia data $%s: %s"
      Data.pp_elt elt (Data.name d) msg ()

  let add m =
    let* init = getenv in
    let* env = Module.data m |> M.Seq.fold ~init ~f:(fun env d ->
        M.lift_err @@ Env.add_data d env) in
    updenv env

  let check d = Data.elts d |> M.Seq.iter ~f:(function
      | #const | `string _ -> !!()
      | `zero n when n >= 1 -> !!()
      | `zero _ as elt ->
        invalid_elt d (elt :> Data.elt)
          "argument must be greater than 0")
end

(* Checking type definitions. *)

module Types = struct
  let add m =
    let* init = getenv in
    let* env = Module.typs m |> M.Seq.fold ~init ~f:(fun env t ->
        M.lift_err @@ Env.add_typ t env) in
    updenv env

  let check =
    let* env = getenv in
    Type.layouts_of_types (Map.data env.tenv) >>?
    M.List.fold ~init:env ~f:(fun env (name, l) ->
        match Map.add env.genv ~key:name ~data:l with
        | `Ok genv -> !!{env with genv}
        | `Duplicate ->
          M.failf "Redefinition of layout for :%s"
            name ()) >>= updenv
end

(* Main procedure. *)

let check m =
  let* () = Types.add m in
  let* () = Types.check in
  let* () = Datas.add m in
  let* () = Funcs.add m in
  let* () = Module.data m |> M.Seq.iter ~f:Datas.check in
  let* () = Module.funs m |> M.Seq.iter ~f:Funcs.check in
  !!()

let reject e = Error e
let accept _ ctx = Ok ctx.env

let run m ~target = (check m).run {
    env = Env.create target;
    fn = None;
    blk = None;
    ins = None;
  } ~reject ~accept

(* Updating the environment when a function definition is transformed. *)

let remove_fn fn =
  let name = Func.name fn in
  M.update @@ fun ctx -> {
    ctx with env = {
      ctx.env with
      fenv = Map.remove ctx.env.fenv name;
      venv = Map.remove ctx.env.venv name;
    }}

let add_fn fn =
  let* env = getenv in
  let*? env = Env.add_fn fn env in
  updenv env

let update_fn env fn =
  let go =
    let* () = remove_fn fn in
    let* () = add_fn fn in
    let* () = Funcs.check fn in
    !!() in
  go.run {
    env;
    fn = None;
    blk = None;
    ins = None;
  } ~reject ~accept

let update_fns env fns =
  let go =
    let* () = M.List.iter fns ~f:remove_fn in
    let* () = M.List.iter fns ~f:add_fn in
    let* () = M.List.iter fns ~f:Funcs.check in
    !!() in
  go.run {
    env;
    fn = None;
    blk = None;
    ins = None;
  } ~reject ~accept
