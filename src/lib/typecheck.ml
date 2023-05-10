open Core
open Regular.Std
open Graphlib.Std
open Virtual

let unify_fail t t' v fn = Or_error.errorf
    "Failed to unify types '%a' and '%a' for var %a in function %s"
    Type.pps t Type.pps t' Var.pps v @@ Func.name fn

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
    | `Duplicate -> Or_error.errorf "Redefinition of data %s" name
    | `Ok denv -> Ok {env with denv}

  (* If we don't have the data defined in the module, then assume it is
     external (i.e. it is linked with our program a posteriori), and that
     the user accepts the risk. *)
  let typeof_data name env = Map.find env.denv name

  let add_fn fn env =
    let name = Func.name fn in
    match Map.add env.fenv ~key:name ~data:(Func.typeof fn) with
    | `Duplicate -> Or_error.errorf "Redefinition of function %s" name
    | `Ok fenv -> Ok {env with fenv}

  (* If we don't have the function defined in the module, then assume
     it is external (i.e. it is linked with our program a posteriori),
     and that the user accepts the risk. *)
  let typeof_fn name env = Map.find env.fenv name

  let add_typ (t : Type.compound) env =
    let name = match t with
      | `compound (name, _, _) -> name in
    match Map.add env.tenv ~key:name ~data:t with
    | `Duplicate -> Or_error.errorf "Redefinition of type %s" name
    | `Ok tenv -> Ok {env with tenv}

  let typeof_typ name env = match Map.find env.tenv name with
    | None -> Or_error.errorf "Undefined type %s" name
    | Some t -> Ok t

  let typeof_var fn v env =
    let fname = Func.name fn in
    match Map.find env.venv fname with
    | None ->
      Or_error.errorf
        "No function %s in environment for variable %a"
        fname Var.pps v
    | Some m -> match Map.find m v with
      | Some t -> Ok t
      | None ->
        Or_error.errorf
          "No variable %a in function %s"
          Var.pps v fname

  exception Unify_fail of Type.t

  let add_var fn v t env = try
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

  let add_layout t env =
    let name = match t with
      | `compound (name, _, _) -> name in
    let gamma name = match layout name env with
      | Error err -> failwithf "%s" (Error.to_string_hum err) ()
      | Ok l -> l in
    try match Map.add env.genv ~key:name ~data:(Type.layout gamma t) with
      | `Duplicate -> Or_error.errorf "Redefinition of type %s" name
      | `Ok genv -> Ok {env with genv}
    with
      | Invalid_argument msg
      | Failure msg -> Or_error.errorf "%s" msg
end

type env = Env.t

module M = Sm.Make(struct
    type state = env
    let fail msg = Error.createf "Type error: %s" msg
  end)

include M.Syntax

type 'a t = 'a M.m

let max_i8  = Bitvec.of_string "0xff"
let max_i16 = Bitvec.of_string "0xffff"
let max_i32 = Bitvec.of_string "0xffffffff"
let max_i64 = Bitvec.of_string "0xffffffffffffffff"

let max_of_imm : Type.imm -> Bitvec.t = function
  | `i8  -> max_i8
  | `i16 -> max_i16
  | `i32 -> max_i32
  | `i64 -> max_i64

let check_max i t =
  let m = max_of_imm t in
  if Bitvec.(i > m) then
    M.fail @@ Error.of_string @@ Format.asprintf
      "Integer %a does not fit in type %a"
      Bitvec.pp i Type.pp_imm t
  else !!(t :> Type.t)

let typeof_const : const -> Type.t t = function
  | `int (i, t) -> check_max i t
  | `float _ -> !!`f32
  | `double _ -> !!`f64
  | `sym _ ->
    let+ t = M.gets Env.target in
    (Target.word t :> Type.t)

let typeof_arg fn env : operand -> Type.t t = function
  | #const as c -> typeof_const c
  | `var v -> M.lift_err @@ Env.typeof_var fn v env

let add_typs m =
  let* init = M.get () in
  let* env = Module.typs m |> M.Seq.fold ~init ~f:(fun env t ->
      M.lift_err @@ Env.add_typ t env) in
  M.put env

let add_datas m =
  let* init = M.get () in
  let* env = Module.data m |> M.Seq.fold ~init ~f:(fun env d ->
      M.lift_err @@ Env.add_data d env) in
  M.put env

let add_funs m =
  let* init = M.get () in
  let* env = Module.funs m |> M.Seq.fold ~init ~f:(fun env fn ->
      M.lift_err @@ Env.add_fn fn env) in
  M.put env

let blk_args fn blk =
  let* init = M.get () in
  let* env = Blk.args blk |> M.Seq.fold ~init ~f:(fun env (v, t) ->
      M.lift_err @@ Env.add_var fn v (t :> Type.t) env) in
  M.put env

let expect_ptr_size_base_var fn blk l v t word msg =
  let word = Format.asprintf "%a" Type.pp_imm_base word in
  M.fail @@ Error.createf
    "Expected imm_base of type %s for var %a in %s %a \
     in block %a in function %s, got %a"
    word Var.pps v msg Label.pps l Label.pps (Blk.label blk)
    (Func.name fn) Type.pps t

let expect_ptr_size_var fn blk l v t msg =
  M.fail @@ Error.createf
    "Expected imm_base type for var %a in %s %a in \
     block %a in function %s, got %a"
    Var.pps v msg Label.pps l Label.pps (Blk.label blk)
    (Func.name fn) Type.pps t 

let expect_ptr_size_base_arg fn blk l a t word msg =
  let a = Format.asprintf "%a" pp_operand a in
  let word = Format.asprintf "%a" Type.pp_imm_base word in
  M.fail @@ Error.createf
    "Expected imm_base of size %s for arg %s in %s %a \
     in block %a in function %s, got %a"
    word a msg Label.pps l Label.pps (Blk.label blk)
    (Func.name fn) Type.pps t

let unify_fail_arg fn blk l t a t' =
  let a = Format.asprintf "%a" pp_operand a in
  M.fail @@ Error.createf
    "Expected type %a for arg %s in instruction %a in \
     block %a in function %s, got %a"
    Type.pps t a Label.pps l Label.pps
    (Blk.label blk) (Func.name fn) Type.pps t'

let unify_arg fn blk l ta a t = match ta, t with
  | #Type.t as ta, _ ->
    let t = (t :> Type.t) in        
    if Type.(ta = t) then !!() else unify_fail_arg fn blk l t a ta

type binop_typ = [
  | Type.basic
  | `flag
]

let op_arith_binop fn blk l tl al tr ar (o : Insn.arith_binop) =
  let t = match o with
    | `add t
    | `div t
    | `mul t
    | `rem t
    | `sub t -> t
    | `mulh t
    | `udiv t
    | `urem t -> (t :> Type.basic) in
  let* () = unify_arg fn blk l tl al t in
  let+ () = unify_arg fn blk l tr ar t in
  (t :> binop_typ)

let op_bitwise_binop fn blk l tl al tr ar (o : Insn.bitwise_binop) =
  let t = match o with
    | `and_ t
    | `or_ t
    | `asr_ t
    | `lsl_ t
    | `lsr_ t
    | `rol t
    | `ror t
    | `xor t -> t in
  let* () = unify_arg fn blk l tl al t in
  let+ () = unify_arg fn blk l tr ar t in
  (t :> binop_typ)

let op_cmp fn blk l tl al tr ar (o : Insn.cmp) =
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
  let* () = unify_arg fn blk l tl al t in
  let+ () = unify_arg fn blk l tr ar t in
  `flag

let op_arith_unop fn blk l ta a (o : Insn.arith_unop) =
  let t = match o with
    | `neg t -> t in
  let+ () = unify_arg fn blk l ta a t in
  t

let op_bitwise_unop fn blk l ta a (o : Insn.bitwise_unop) =
  let t = match o with
    | `not_ t -> t in
  let+ () = unify_arg fn blk l ta a t in
  (t :> Type.basic)

let unify_fp_fail fn blk l t a =
  let a = Format.asprintf "%a" pp_operand a in
  M.fail @@ Error.createf
    "Expected floating point type for arg %s in instruction %a \
     in block %a in function %s, got %a" a Label.pps l Label.pps
    (Blk.label blk) (Func.name fn) Type.pps t

let unify_imm_fail fn blk l t a =
  let a = Format.asprintf "%a" pp_operand a in
  M.fail @@ Error.createf
    "Expected immediate type for arg %s in instruction %a \
     in block %a in function %s, got %a" a Label.pps l Label.pps
    (Blk.label blk) (Func.name fn) Type.pps t

let unify_mem_fail fn blk l t v =
  M.fail @@ Error.createf
    "Expected mem type for var %a in instruction %a \
     in block %a in function %s, got %a" Var.pps v Label.pps l
    Label.pps (Blk.label blk) (Func.name fn) Type.pps t

let unify_flag_fail fn blk l t v =
  M.fail @@ Error.createf
    "Expected mem type for var %a in instruction %a \
     in block %a in function %s, got %a" Var.pps v Label.pps l
    Label.pps (Blk.label blk) (Func.name fn) Type.pps t

let unify_fext_fail fn blk l t a =
  let a = Format.asprintf "%a" pp_operand a in
  M.fail @@ Error.createf
    "Invalid floating point type %a for arg %s in instruction %a \
     in block %a in function %s" Type.pps t a Label.pps l Label.pps
    (Blk.label blk) (Func.name fn)

let op_cast fn blk l ta a : Insn.cast -> Type.basic t = function
  | `bits t -> !!t
  | `fext t ->
    let+ () = match t, ta with
      | `f64, `f64
      | `f64, `f32
      | `f32, `f32 -> !!()
      | _, #Type.fp -> unify_fext_fail fn blk l ta a
      | _ -> unify_fp_fail fn blk l ta a in
    (t :> Type.basic)
  | `ftosi (tf, ti)
  | `ftoui (tf, ti) ->
    let+ () = unify_arg fn blk l ta a (tf :> Type.t) in
    (ti :> Type.basic)
  | `ftrunc t ->
    let+ () = match ta with
      | #Type.fp -> !!()
      | _ -> unify_fp_fail fn blk l ta a in
    (t :> Type.basic)
  | `itrunc t | `sext t | `zext t ->
    let+ () = match ta with
      | #Type.imm -> !!()
      | _ -> unify_imm_fail fn blk l ta a in
    (t :> Type.basic)
  | `sitof (ti, tf)
  | `uitof (ti, tf) ->
    let+ () = unify_arg fn blk l ta a (ti :> Type.t) in
    (tf :> Type.basic)

let op_copy fn blk l ta a : Insn.copy -> Type.basic t = function
  | `copy t -> match ta, t with
    | #Type.compound, #Type.imm -> !!t
    | #Type.t as ta, t ->
      let t' = (t :> Type.t) in
      if Type.(ta = t') then !!t
      else unify_fail_arg fn blk l t' a ta

let op_binop fn blk l env v b al ar =
  let* tl = typeof_arg fn env al in
  let* tr = typeof_arg fn env ar in
  let* t = match b with
    | #Insn.arith_binop as o ->
      op_arith_binop fn blk l tl al tr ar o
    | #Insn.bitwise_binop as o ->
      op_bitwise_binop fn blk l tl al tr ar o
    | #Insn.cmp as o ->
      op_cmp fn blk l tl al tr ar o in
  M.lift_err @@ Env.add_var fn v (t :> Type.t) env

let op_unop fn blk l env v u a =
  let* ta = typeof_arg fn env a in
  let* t = match u with
    | #Insn.arith_unop as o ->
      op_arith_unop fn blk l ta a o
    | #Insn.bitwise_unop as o ->
      op_bitwise_unop fn blk l ta a o
    | #Insn.cast as o ->
      op_cast fn blk l ta a o
    | #Insn.copy as o ->
      op_copy fn blk l ta a o in
  M.lift_err @@ Env.add_var fn v (t :> Type.t) env

let op_mem_load fn blk l env word t m a =
  let*? tm = Env.typeof_var fn m env in
  let* () = match tm with
    | `mem -> !!()
    | _ -> unify_mem_fail fn blk l tm m in
  let* ta = typeof_arg fn env a in
  let+ () = unify_arg fn blk l ta a (word :> Type.t) in
  (t :> Type.t)

let op_mem_store fn blk l env word t m a v =
  let*? tm = Env.typeof_var fn m env in
  let* () = match tm with
    | `mem -> !!()
    | _ -> unify_mem_fail fn blk l tm m in
  let* ta = typeof_arg fn env a in
  let* _tv = typeof_arg fn env v in
  let* () = unify_arg fn blk l ta a (word :> Type.t) in
  let+ () = unify_arg fn blk l ta a (t :> Type.t) in
  `mem

let invalid_alloc fn blk l n =
  M.fail @@ Error.createf
    "In alloc instruction %a of block %a in function %s: \
     invalid size %d, must be greater than zero" Label.pps l
    Label.pps (Blk.label blk) (Func.name fn) n

let op_mem fn blk l env v m =
  let* word = M.gets @@ Fn.compose Target.word Env.target in
  let* t = match m with
    | `alloc n when n <= 0 -> invalid_alloc fn blk l n
    | `alloc _n -> !!(word :> Type.t)
    | `load (t, m, a) -> op_mem_load fn blk l env word t m a
    | `store (t, m, a, v) -> op_mem_store fn blk l env word t m a v in
  M.lift_err @@ Env.add_var fn v t env

let op_sel fn blk l env v t c al ar =
  let*? tc = Env.typeof_var fn c env in
  let* () = match tc with
    | `flag -> !!()
    | _ -> unify_flag_fail fn blk l tc c in
  let* tl = typeof_arg fn env al in
  let* tr = typeof_arg fn env ar in
  let* () = unify_arg fn blk l tl al (t :> Type.t) in
  let* () = unify_arg fn blk l tr ar (t :> Type.t) in
  M.lift_err @@ Env.add_var fn v (t :> Type.t) env

let op_basic fn blk l env : Insn.basic -> env t = function
  | `bop (v, b, al, ar) -> op_binop fn blk l env v b al ar
  | `uop (v, u, a) -> op_unop fn blk l env v u a
  | `mem (v, m) -> op_mem fn blk l env v m
  | `sel (v, t, c, al, ar) -> op_sel fn blk l env v t c al ar

let unify_fail_void_call fn blk l t s =
  let t = Format.asprintf "%a" Type.pp_arg t in
  M.fail @@ Error.createf
    "Failed to unify return types %s and <void> for \
     call at %a to function %s in block %a of function %s"
    t Label.pps l s Label.pps (Blk.label blk) (Func.name fn)

let unify_fail_call_ret fn blk l t1 t2 s =
  let ts = Format.asprintf "%a and %a" Type.pp_arg t1 Type.pp_arg t2 in
  M.fail @@ Error.createf
    "Failed to unify return types %s for \
     call at %a to function %s in block %a of function %s"
    ts Label.pps l s Label.pps (Blk.label blk) (Func.name fn)

let non_variadic_call fn blk l s =
  M.fail @@ Error.createf
    "Variadic call at %a to non-variadic function %s in \
     block %a of function %s" Label.pps l s Label.pps
    (Blk.label blk) (Func.name fn)

let unequal_lengths_call fn blk l s args targs =
  M.fail @@ Error.createf
    "Call at %a to function %s in block %a of function %s: \
     expected %d arguments, got %d" Label.pps l s Label.pps
    (Blk.label blk) (Func.name fn) (List.length targs)
    (List.length args)

let unify_fail_call_arg fn blk l s t a t' =
  let a = Format.asprintf "%a" pp_operand a in
  M.fail @@ Error.createf
    "Call at %a to function %s in block %a of function %s: \
     expected %a for arg %s, got %a" Label.pps l s Label.pps
    (Blk.label blk) (Func.name fn) Type.pps t a Type.pps t'

let name_arg_expected_imm fn blk l s t a n =
  let a = Format.asprintf "%a" pp_operand a in
  M.fail @@ Error.createf
    "Call at %a to function %s in block %a of function %s: \
     expected pointer-sized immediate for :%s arg %s, got %a"
    Label.pps l s Label.pps (Blk.label blk) (Func.name fn)
    n a Type.pps t

let check_call_var fn blk l env _t _args _vargs v =
  let*? t = Env.typeof_var fn v env in
  let* word = M.gets @@ Fn.compose Target.word Env.target in
  (* No guarantees for indirect call, just make sure that
     the var is pointer-sized. *)
  match t with
  | #Type.imm_base as b ->
    if Type.equal_imm_base b word then !!()
    else expect_ptr_size_base_var fn blk l v t word "call"
  | _ -> expect_ptr_size_var fn blk l v t "call"

let check_call_sym_ret fn blk l t ret s = match t, ret with
  | None, Some t -> unify_fail_void_call fn blk l (t :> Type.arg) s
  | Some t, None -> unify_fail_void_call fn blk l t s
  | Some t1, Some t2 when Type.equal_arg t1 (t2 :> Type.arg) -> !!()
  | Some t1, Some t2 -> unify_fail_call_ret fn blk l t1 (t2 :> Type.arg) s
  | None, None -> !!()

let check_call_sym_variadic fn blk l s vargs variadic =
  if variadic || List.is_empty vargs then !!()
  else non_variadic_call fn blk l s

let check_call_sym_args fn blk l env _t s = M.List.iter ~f:(fun (a, t) ->
    let* at = typeof_arg fn env a in
    let* word = M.gets @@ Fn.compose Target.word Env.target in
    match at, t with
    | #Type.imm_base as b, `name _ ->
      (* If the argument has a named type (i.e. a compound)
         then it is expected to be passed as a pointer. *)
      let bt = (b :> Type.t) in
      if Type.equal_imm_base b word then !!()
      else expect_ptr_size_base_arg fn blk l a bt word "call"
    | #Type.t as at, `name n ->
      (* Fail otherwise. *)
      name_arg_expected_imm fn blk l s at a n
    | (#Type.t as at), (#Type.basic as t) ->
      (* Normal unification. *)
      let t = (t :> Type.t) in
      if Type.(at = t) then !!()
      else unify_fail_call_arg fn blk l s t a at)

let check_call_sym fn blk l env t args vargs s ret targs variadic =
  let* () = check_call_sym_ret fn blk l t ret s in
  let* () = check_call_sym_variadic fn blk l s vargs variadic in
  match List.zip args targs with
  | Unequal_lengths -> unequal_lengths_call fn blk l s args targs
  | Ok z -> check_call_sym_args fn blk l env t s z

let check_call fn blk l env t args vargs : global -> unit t = function
  | `addr _ -> !!() (* No guarantees for call to raw address. *)
  | `var v -> check_call_var fn blk l env t args vargs v
  | `sym s -> match Env.typeof_fn s env with
    | Some (`proto (ret, targs, variadic)) ->
      check_call_sym fn blk l env t args vargs s ret targs variadic
    | None -> !!() (* No guarantees for an external function. *)

let op_call fn blk l env : Insn.call -> env t = function
  | `call (Some (v, t), g, args, vargs) ->
    let* () =
      let t = Some (t :> Type.arg) in
      check_call fn blk l env t args vargs g in
    M.lift_err @@ Env.add_var fn v (t :> Type.t) env
  | `call (None, g, args, vargs) ->
    let+ () = check_call fn blk l env None args vargs g in
    env

let op_variadic fn blk l env : Insn.variadic -> env t = function
  | `vastart v ->
    let*? t = Env.typeof_var fn v env in
    match t with
    | #Type.imm_base as b ->
      (* Argument is expected to be a pointer. *)
      let* word = M.gets @@ Fn.compose Target.word Env.target in
      if Type.equal_imm_base b word then !!env
      else expect_ptr_size_base_var fn blk l v t word "variadic instruction"
    | _ -> expect_ptr_size_var fn blk l v t "variadic instruction"

let op fn blk l env : Insn.op -> env t = function
  | #Insn.basic    as b -> op_basic    fn blk l env b
  | #Insn.call     as c -> op_call     fn blk l env c
  | #Insn.variadic as v -> op_variadic fn blk l env v

let blk_insns seen fn blk =
  let* init = M.get () in
  let* env = Blk.insns blk |> M.Seq.fold ~init ~f:(fun env d ->
      let l = Insn.label d in
      let o = Insn.op d in
      let*? () = match Hash_set.strict_add seen l with
        | Ok _ as ok -> ok
        | Error _ ->
          Or_error.errorf
            "Instruction for label %a in block %a \
             already exists in function %s"
            Label.pps l Label.pps (Blk.label blk) @@
          Func.name fn in
      op fn blk l env o) in
  M.put env

let unequal_lengths_ctrl fn blk l args targs =
  M.fail @@ Error.createf
    "Jump to %a in block %a of function %s: \
     expected %d arguments, got %d" Label.pps l Label.pps
    (Blk.label blk) (Func.name fn) (List.length targs)
    (List.length args)

let unify_fail_arg_ctrl fn blk l t a t' =
  let a = Format.asprintf "%a" pp_operand a in
  M.fail @@ Error.createf
    "Expected type %a for arg %s in jump to %a in \
     block %a in function %s, got %a"
    Type.pps t a Label.pps l Label.pps
    (Blk.label blk) (Func.name fn) Type.pps t'

let unify_arg_ctrl fn blk l ta a t = match ta, t with
  | #Type.t as ta, _ ->
    let t = (t :> Type.t) in        
    if Type.(ta = t) then !!()
    else unify_fail_arg_ctrl fn blk l t a ta

let check_var_dst fn _blk v =
  let* env = M.get () in
  let word = Target.word @@ Env.target env in
  let*? t = Env.typeof_var fn v env in
  if Type.(t = (word :> Type.t)) then !!()
  else M.lift_err @@ unify_fail t (word :> Type.t) v fn

let check_label_dst blks fn blk l args =
  let* env = M.get () in
  let*? _b = match Map.find blks l with
    | Some b -> Ok b
    | None ->
      Or_error.errorf
        "Jump destination %a at block %a in function %s \
         does not exist." Label.pps l Label.pps (Blk.label blk)
        (Func.name fn) in
  let targs = Seq.to_list @@ Seq.map ~f:snd @@ Blk.args blk in
  match List.zip args targs with
  | Unequal_lengths -> unequal_lengths_ctrl fn blk l args targs
  | Ok z -> M.List.iter z ~f:(fun (a, t) ->
      let* ta = typeof_arg fn env a in
      unify_arg_ctrl fn blk l ta a (t :> Type.t))

let check_dst blks fn blk : dst -> unit t = function
  | `addr _ | `sym _ -> !!()
  | `var v -> check_var_dst fn blk v
  | `label (l, args) -> check_label_dst blks fn blk l args

let unify_flag_fail_ctrl fn blk t v =
  M.fail @@ Error.createf
    "Expected mem type for var %a of jnz in block %a in \
     function %s, got %a" Var.pps v Label.pps (Blk.label blk)
    (Func.name fn) Type.pps t

let unify_fail_void_ret fn blk t =
  M.fail @@ Error.createf
    "Failed to unify return types %a and <void> for \
     ret in block %a of function %s"
    Type.pps t Label.pps (Blk.label blk) (Func.name fn)

let unify_fail_ret fn blk t1 t2 =
  let ts = Format.asprintf "%a and %a" Type.pp t1 Type.pp t2 in
  M.fail @@ Error.createf
    "Failed to unify return types %s for \
     ret in block %a of function %s" ts Label.pps
    (Blk.label blk) (Func.name fn)

let ctrl_br blks fn blk c t f =
  let* env = M.get () in
  let*? tc = Env.typeof_var fn c env in
  let* () = match tc with
    | `flag -> !!()
    | _ -> unify_flag_fail_ctrl fn blk tc c in
  let* () = check_dst blks fn blk t in
  check_dst blks fn blk f

let ctrl_ret_none _blks fn blk = match Func.return fn with
  | Some t -> unify_fail_void_ret fn blk (t :> Type.t)
  | None -> !!()

let ctrl_ret_some _blks fn blk r =
  let* env = M.get () in
  let* tr = typeof_arg fn env r in
  match tr, Func.return fn with
  | t, None -> unify_fail_void_ret fn blk t
  | #Type.t as r, Some t ->
    let t' = (t :> Type.t) in
    if Type.(r = t') then !!()
    else unify_fail_ret fn blk r t'

let ctrl_sw blks fn blk t v d tbl =
  let t = (t :> Type.t) in
  let* env = M.get () in
  let*? tv = Env.typeof_var fn v env in
  if Type.(t = tv) then
    let* () = check_dst blks fn blk (d :> dst) in
    Ctrl.Table.enum tbl |> M.Seq.iter ~f:(fun (_, l) ->
        check_dst blks fn blk (l :> dst))
  else M.lift_err @@ unify_fail t tv v fn

let blk_ctrl blks fn blk = match Blk.ctrl blk with
  | `hlt -> !!()
  | `jmp d -> check_dst blks fn blk d
  | `br (c, t, f) -> ctrl_br blks fn blk c t f
  | `ret None -> ctrl_ret_none blks fn blk
  | `ret (Some r) -> ctrl_ret_some blks fn blk r
  | `sw (t, v, d, tbl) -> ctrl_sw blks fn blk t v d tbl

let not_pseudo = Fn.non Label.is_pseudo

let rec check_blk doms rpo blks seen fn l =
  let*? blk = match Map.find blks l with
    | Some blk -> Ok blk
    | None ->
      Or_error.errorf
        "Invariant broken: block %a is missing"
        Label.pps l in
  let* () = blk_args fn blk in
  let* () = blk_insns seen fn blk in
  let* () = blk_ctrl blks fn blk in
  let rpn = Hashtbl.find_exn rpo in
  Tree.children doms l |> Seq.filter ~f:not_pseudo |> Seq.to_list |>
  List.sort ~compare:(fun a b -> compare (rpn a) (rpn b)) |>
  M.List.iter ~f:(check_blk doms rpo blks seen fn)

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

let fn_args fn =
  let* init = M.get () in
  let* env = Func.args fn |> M.Seq.fold ~init ~f:(fun env (x, t) ->
      let*? t = typ_of_typ_arg env t in
      M.lift_err @@ Env.add_var fn x t env) in
  M.put env

let check_fn fn =
  let* () = fn_args fn in
  (* Be aware of duplicate labels for instructions. *)
  let seen = Label.Hash_set.create () in
  let*? blks = try Ok (Func.map_of_blks fn) with
    | Invalid_argument msg -> Or_error.error_string msg in
  let cfg = Cfg.create fn in
  let start = Label.pseudoentry in
  (* We will traverse the blocks according to the dominator tree
     so that we get the right ordering for definitions. *)
  let doms = Graphlib.dominators (module Cfg) cfg start in
  (* However, it requires us to visit children of each node in
     the tree according to the reverse postorder traversal. *)
  check_blk doms (make_rpo cfg start) blks seen fn @@ Func.entry fn

let invalid_elt d elt msg =
  let elt = Format.asprintf "%a" Data.pp_elt elt in
  M.fail @@ Error.createf
    "Invalid element %s in data %s: %s"
    elt (Data.name d) msg

let check_basic d elt t = M.List.iter ~f:(fun c ->
    let* t' = typeof_const c in
    if Type.equal (t :> Type.t) t' then !!()
    else invalid_elt d elt "type mismatch")

let check_data d = Data.elts d |> M.Seq.iter ~f:(function
    | `basic (t, cs) as elt -> check_basic d elt t cs
    | `string _ | `sym _ -> !!()
    | `zero n when n >= 1 -> !!()
    | `zero _ as elt ->
      invalid_elt d (elt :> Data.elt)
        "argument must be greater than 0")

module TG = Graphlib.Make(String)(Unit)

let check_typ_cycles g env =
  Graphlib.strong_components (module TG) g |>
  Partition.groups |> M.Seq.iter ~f:(fun grp ->
      match Seq.to_list @@ Group.enum grp with
      | [] -> !!()
      | [name] ->
        let `compound (_, _, fields) = Map.find_exn env.Env.tenv name in
        if List.exists fields ~f:(function
            | `name n -> String.(name = n)
            | `elt _ -> false)
        then M.fail @@ Error.createf "Cycle detected in type :%s" name
        else !!()
      | xs ->
        M.fail @@ Error.createf "Cycle detected in types %s" @@
        List.to_string ~f:(fun s -> ":" ^ s) xs)

let check_typs =
  let* env = M.get () in
  (* Construct the graph and also check for undeclared type names. *)
  let* g =
    Map.data env.tenv |>
    M.List.fold ~init:TG.empty ~f:(fun g -> function
        | `compound (name, _, fields) ->
          let init = TG.Node.insert name g in
          M.List.fold fields ~init ~f:(fun g -> function
              | `elt _ -> !!g
              | `name n when Map.mem env.tenv n ->
                !!TG.Edge.(insert (create name n ()) g)
              | `name n ->
                M.fail @@ Error.createf
                  "Undeclared type field :%s in type :%s"
                  n name)) in
  let* () = check_typ_cycles g env in
  (* Fill gamma, now that we know there is a topological ordering. *)
  let* env =
    Graphlib.postorder_traverse (module TG) g |>
    M.Seq.fold ~init:env ~f:(fun env name ->
        let t = Map.find_exn env.tenv name in
        M.lift_err @@ Env.add_layout t env) in
  M.put env

let check m =
  let* () = add_typs m in
  let* () = check_typs in
  let* () = add_datas m in
  let* () = add_funs m in
  let* () = Module.data m |> M.Seq.iter ~f:check_data in
  let* () = Module.funs m |> M.Seq.iter ~f:check_fn in
  !!()

let run m ~target =
  Env.create target |> (check m).run
    ~reject:(fun err -> Error err)
    ~accept:(fun () env -> Ok env)
