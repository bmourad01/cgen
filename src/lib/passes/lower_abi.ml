(* Lower a function according to the System V ABI (AMD64). *)

open Core
open Regular.Std
open Graphlib.Std
open Virtual

module Cv = Context.Virtual

open Context.Syntax

(* RDI, RSI, RDX, RCX, R8, R9 *)
let num_int_args = 6

let int_args = [|
  "RDI";
  "RSI";
  "RDX";
  "RCX";
  "R8";
  "R9";
|]

let int_rets = [|
  "RAX";
  "RDX";
|]

(* XMM0, XMM1, ..., XMM7 *)
let num_sse_args = 8

let sse_args =
  Array.init num_sse_args ~f:(Format.sprintf "XMM%d")

let sse_rets = [|
  "XMM0";
  "XMM1";
|]

type reg =
  | Rnone
  | Rint
  | Rsse
[@@deriving equal]

let reg_type = function
  | Rnone | Rint -> `i64
  | Rsse -> `f64

(* Integer registers have precedence. *)
let merge_reg this that = match this with
  | Rnone -> that
  | Rint -> this
  | Rsse -> match that with
    | Rint -> that
    | Rsse | Rnone -> this

type cls =
  | Kreg of reg * reg
  | Kmem

(* `size` and `align` are always multiples of 8. *)
type acls = {
  size  : int;
  align : int;
  cls   : cls;
}

let classify_layout lt =
  let size = Type.Layout.sizeof lt in
  (* Align to the nearest eightbyte boundary. *)
  let align = max 8 @@ Type.Layout.align lt in
  let size = (size + align - 1) land -align in
  let cls =
    (* Try to pack the struct into two registers. If it is
       larger than 16 bytes or contains unaligned fields
       then it will be passed on the stack. *)
    if size <= 16 then
      Type.Layout.data lt |> Seq.fold_until
        ~init:(Rnone, Rnone, 0)
        ~finish:(fun (r1, r2, _) -> Kreg (r1, r2))
        ~f:(fun (r1, r2, s) -> function
            | #Type.imm as m ->
              let s' = s + (Type.sizeof_imm m / 8) in
              begin match s / 8 with
                | 0 -> Continue (Rint, r2, s')
                | 1 -> Continue (r1, Rint, s;)
                | _ -> assert false
              end
            | #Type.fp as f ->
              let s' = s + (Type.sizeof_fp f / 8) in
              begin match s / 8 with
                | 0 -> Continue (merge_reg r1 Rsse, r2, s')
                | 1 -> Continue (r1, merge_reg r2 Rsse, s')
                | _ -> assert false
              end
            | `pad n -> Continue (r1, r2, s + n)
            | `opaque _ -> Stop Kmem)
    else Kmem in
  {size; align; cls}

type ret = {
  reti : Abi.insn list; (* Copy the data to be returned. *)
  retr : string list;   (* Registers to return in. *)
}

let empty_ret = {
  reti = [];
  retr = [];
}

type call = {
  callai : Abi.insn Ftree.t;    (* Set up the arguments before the call. *)
  callar : string Ftree.t;      (* Passing register arguments. *)
  callam : Abi.operand Ftree.t; (* Passing memory arguments. *)
  callri : Abi.insn Ftree.t;    (* Copy the return value after the call. *)
  callrr : string list;         (* Registers holding the return value. *)
}

let empty_call = {
  callai = Ftree.empty;
  callar = Ftree.empty;
  callam = Ftree.empty;
  callri = Ftree.empty;
  callrr = [];
}

let (@!) t l = Ftree.(append t @@ of_list l)

type param = {
  pty  : Type.basic;
  pvar : Abi.var;
  pins : Abi.insn list;
}

type env = {
  fn           : func;                      (* The original function. *)
  blks         : blk Label.Tree.t;          (* Map of basic blocks. *)
  doms         : Label.t tree;              (* Dominator tree. *)
  tenv         : Typecheck.env;             (* Typing environment. *)
  rets         : ret Label.Table.t;         (* Lowered `ret` instructions. *)
  calls        : call Label.Table.t;        (* Lowered `call` instructions. *)
  refs         : Var.t Var.Table.t;         (* Canonicalization of `ref`s *)
  unrefs       : Abi.insn list Var.Table.t; (* `unref` to store. *)
  canon_ref    : Var.t Var.Table.t;         (* Canonicalize `ref`s. *)
  slots        : slot Vec.t;                (* New stack slots. *)
  params       : param Vec.t;               (* Function parameters. *)
  mutable rmem : Var.t option;              (* Return value blitted to memory. *)
}

let init_env tenv fn =
  let cfg = Cfg.create fn in
  let doms = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in {
    fn;
    blks = Func.map_of_blks fn;
    doms;
    tenv;
    rets = Label.Table.create ();
    calls = Label.Table.create ();
    refs = Var.Table.create ();
    unrefs = Var.Table.create ();
    canon_ref = Var.Table.create ();
    slots = Vec.create ();
    params = Vec.create ();
    rmem = None;
  }

(* Iterate over the dominator tree. *)
let iter_blks env ~f =
  let rec loop q = match Stack.pop q with
    | None -> !!()
    | Some l ->
      let* () = match Label.Tree.find env.blks l with
        | None -> !!()
        | Some b -> f b in
      Tree.children env.doms l |>
      Seq.iter ~f:(Stack.push q);
      loop q in
  loop @@ Stack.singleton @@ Func.entry env.fn

let new_slot env size align =
  let* x = Context.Var.fresh in
  let*? s = Slot.create x ~size ~align in
  Vec.push env.slots s;
  !!x

let find_ref env x = match Hashtbl.find env.refs x with
  | Some y -> y
  | None ->
    failwithf "%a has no ref in function $%s"
      Var.pps x (Func.name env.fn) ()

let o8 = `int (Bv.M64.int 8, `i64)

let oper (o : operand) = (o :> Abi.operand)

let typeof_var env x =
  Context.lift_err @@ Typecheck.Env.typeof_var env.fn x env.tenv

let word env = (Target.word (Typecheck.Env.target env.tenv) :> Type.t)

let typeof_operand env : operand -> Type.t Context.t = function
  | `int (_, t) -> !!(t :> Type.t)
  | `bool _ -> !!`flag
  | `float _ -> !!`f32
  | `double _ -> !!`f64
  | `sym _ -> !!(word env)
  | `var x -> typeof_var env x

module Params = struct
  let init_regs env =
    let ni = ref num_int_args and ns = ref num_sse_args in
    let+ () = match Func.return env.fn with
      | Some (#Type.basic | `si8 | `si16 | `si32) | None -> !!()
      | Some `name n ->
        let*? lt = Typecheck.Env.layout n env.tenv in
        match classify_layout lt with
        | {cls = Kmem; _} ->
          let r = int_args.(0) in
          let* x = Context.Var.fresh in
          let+ i = Cv.Abi.insn @@ `uop (`var x, `copy `i64, `reg r) in
          let p = {pty = `i64; pvar = `reg r; pins = [i]} in
          Vec.push env.params p;
          env.rmem <- Some x;
          decr ni
        | _ -> !!() in
    (* Try to allocate the parameter to a register. If we've run out,
       then it is implicitly passed in memory. *)
    function
    | #Type.imm when !ni < 1 -> None
    | #Type.fp when !ns < 1 -> None
    | #Type.imm ->
      let r = int_args.(num_int_args - !ni) in
      decr ni; Some r
    | #Type.fp ->
      let r = sse_args.(num_sse_args - !ns) in
      decr ns; Some r

  let basic_param ~reg env t x =
    let+ pvar, pins = match reg t with
      | None -> !!(`var x, [])
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`var x, `copy t, `reg r) in
        `reg r, [i] in
    Vec.push env.params @@ {pty = t; pvar; pins}

  (* Pass in a single register, so we can reuse `x`. *)
  let onereg_param ~reg env t x y r =
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
  let tworeg_param ~reg env t x y r1 r2 =
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let* x1 = Context.Var.fresh in
    let* x2 = Context.Var.fresh in
    let* o, oi = Cv.Abi.binop (`add `i64) (`var y) o8 in
    let* st1 = Cv.Abi.store t1 (`var x1) (`var y) in
    let* st2 = Cv.Abi.store t1 (`var x1) (`var o) in
    let* pvar1, pins1 = match reg t1 with
      | None -> !!(`var x1, [st1])
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`var x1, `copy t1, `reg r) in
        `reg r, [i; st1] in
    let+ pvar2, pins2 = match reg t2 with
      | None -> !!(`var x2, [oi; st2])
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`var x2, `copy t1, `reg r) in
        `reg r, [i; oi; st2] in
    let p1 = {pty = t1; pvar = pvar1; pins = pins1} in
    let p2 = {pty = t2; pvar = pvar2; pins = pins2} in
    Vec.push env.params p1;
    Vec.push env.params p2

  (* Blit the structure to a stack slot. *)
  let memory_param env t x y size =
    Seq.init (size / 8) ~f:(fun i -> Bv.M64.int (i * 8)) |>
    Context.Seq.iter ~f:(fun ofs ->
        let* x = Context.Var.fresh in
        let+ pins =
          if Bv.(ofs = zero) then
            let+ st = Cv.Abi.store `i64 (`var x) (`var y) in
            [st]
          else
            let ofs = `int (ofs, `i64) in
            let* o, oi = Cv.Abi.binop (`add `i64) (`var y) ofs in
            let+ st = Cv.Abi.store `i64 (`var x) (`var o) in
            [oi; st] in
        let p = {pty = `i64; pvar = `var x; pins} in
        Vec.push env.params p)

  (* Lower the parameters of the function and copy their contents
     to SSA variables or stack slots. *)
  let lower env =
    let* reg = init_regs env in
    Func.args env.fn |>
    Context.Seq.iter ~f:(fun (x, t) -> match t with
        | #Type.basic as t -> basic_param ~reg env t x
        | `name s ->
          let*? lt = Typecheck.Env.layout s env.tenv in
          let k = classify_layout lt in
          let* y = new_slot env k.size k.align in
          Hashtbl.set env.refs ~key:x ~data:y;
          match k.cls with
          | Kreg _ when k.size = 0 -> !!()
          | Kreg (r, _) when k.size = 8 -> onereg_param ~reg env t x y r
          | Kreg (r1, r2) -> tworeg_param ~reg env t x y r1 r2
          | Kmem -> memory_param env t x y k.size)
end

module Refs = struct
  let fresh_ref env s x y =
    let*? lt = Typecheck.Env.layout s env.tenv in
    let k = classify_layout lt in
    let*? s = Slot.create x ~size:k.size ~align:k.align in
    Context.return begin
      Hashtbl.set env.refs ~key:y ~data:x;
      Vec.push env.slots s
    end

  let make_ref env i b x y = match Hashtbl.find env.refs y with
    | Some z -> !!(Hashtbl.set env.canon_ref ~key:x ~data:z)
    | None -> typeof_var env y >>= function
      | `compound (s, _, _) | `opaque (s, _, _) ->
        fresh_ref env s x y
      | t ->
        Context.failf
          "Expected compound type for instruction %a \
           in block %a of function $%s, got %a"
          Insn.pp i Label.pp (Blk.label b)
          (Func.name env.fn) Type.pp t ()

  let make_unref env x s a =
    if not @@ Hashtbl.mem env.refs x then
      let*? lt = Typecheck.Env.layout s env.tenv in
      let k = classify_layout lt in
      let* y = new_slot env k.size k.align in
      let* src, srci = match a with
        | `var x -> !!(x, [])
        | _ ->
          let+ x, i = Cv.Abi.unop (`copy `i64) (oper a) in
          x, [i] in
      let+ blit = Cv.Abi.blit ~src:(`var src) ~dst:(`var y) `i64 k.size in
      Hashtbl.set env.unrefs ~key:x ~data:(srci @ blit);
      Hashtbl.set env.refs ~key:x ~data:y
    else !!()

  (* Change `ref`s of structs to stack slots. *)
  let canonicalize env = iter_blks env ~f:(fun b ->
      let* () =
        Blk.args b |> Context.Seq.iter ~f:(fun x ->
            typeof_var env x >>| function
            | #Type.compound ->
              Hashtbl.set env.refs ~key:x ~data:x
            | _ -> ()) in
      Blk.insns b |> Context.Seq.iter ~f:(fun i ->
          match Insn.op i with
          | `ref (x, `var y) -> make_ref env i b x y
          | `unref (x, s, a) -> make_unref env x s a
          | _ -> !!()))
end

module Rets = struct
  let expect_ret_var env l : operand -> Var.t Context.t = function
    | `var x -> !!x
    | x ->
      Context.failf
        "Expected var for `ret` operand in block %a \
         of function $%s, got %a" Label.pp l
        (Func.name env.fn) pp_operand x ()

  (* Return in the first integer register. *)
  let intret env t key x =
    let reg = int_rets.(0) in
    let u = match t with
      | `i8 | `i16 | `i32 -> `zext `i64
      | `i64 -> `copy `i64 in
    let+ r = Cv.Abi.insn @@ `uop (`reg reg, u, oper x) in
    Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}

  (* Return in the first integer register, with a sign extension. *)
  let intret_signed env key x =
    let reg = int_rets.(0) in
    let+ r = Cv.Abi.insn @@ `uop (`reg reg, `sext `i64, oper x) in
    Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}

  (* Return in the first SSE register. *)
  let sseret env t key x =
    let reg = sse_rets.(0) in
    let+ r = Cv.Abi.insn @@ `uop (`reg reg, `copy t, oper x) in
    Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}

  (* Struct is returned in a single register. *)
  let onereg_ret env r k key x =
    let* x = expect_ret_var env key x in
    let x = find_ref env x in
    let t = reg_type r in
    let reg = match t with
      | `i64 -> int_rets.(0)
      | `f64 -> sse_rets.(0) in
    let+ r = Cv.Abi.insn @@ `load (`reg reg, t, `var x) in
    Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}

  (* Struct is returned in two registers of varying classes. *)
  let tworeg_ret env r1 r2 k key x =
    let* x = expect_ret_var env key x in
    let x = find_ref env x in
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let ni = ref 0 and ns = ref 0 in
    let reg1 = match t1 with
      | `i64 -> incr ni; int_rets.(0)
      | `f64 -> incr ns; sse_rets.(0) in
    let reg2 = match t2 with
      | `i64 -> int_rets.(!ni)
      | `f64 -> sse_rets.(!ns) in
    let* ld1 = Cv.Abi.insn @@ `load (`reg reg1, `i64, `var x) in
    let* a, add = Cv.Abi.binop (`add `i64) (`var x) o8 in
    let+ ld2 = Cv.Abi.insn @@ `load (`reg reg2, `i64, `var a) in
    Hashtbl.set env.rets ~key ~data:{
      reti = [ld1; add; ld2];
      retr = [reg1; reg2]
    }

  (* Struct is blitted to a pointer held by by the implicit
     first argument of the function. This pointer becomes the
     return value. *)
  let memory_ret env k key x =
    let* x = expect_ret_var env key x in
    let src = find_ref env x in
    let dst = match env.rmem with
      | None -> assert false
      | Some dst -> dst in
    let* blit = Cv.Abi.blit `i64 k.size ~src:(`var src) ~dst:(`var dst) in
    let reg = int_rets.(0) in
    let+ r = Cv.Abi.insn @@ `uop (`reg reg, `copy `i64, `var dst) in
    Hashtbl.set env.rets ~key ~data:{
      reti = blit @ [r];
      retr = [reg]
    }

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
    | Some (#Type.imm as t) -> go @@ intret env t
    | Some (`si8 | `si16 | `si32) -> go @@ intret_signed env
    | Some (#Type.fp as t) -> go @@ sseret env t
    | Some `name n ->
      let*? lt = Typecheck.Env.layout n env.tenv in
      let k = classify_layout lt in
      match k.cls with
      | Kreg _ when k.size = 0 -> go @@ fun key _ ->
        (* Struct is empty, so we return nothing. *)
        !!(Hashtbl.set env.rets ~key ~data:empty_ret)
      | Kreg (r, _) when k.size = 8 -> go @@ onereg_ret env r k
      | Kreg (r1, r2) -> go @@ tworeg_ret env r1 r2 k
      | Kmem -> go @@ memory_ret env k
end

module Calls = struct
  (* A compound argument to a call passed in a single register. *)
  let onereg_arg ~dec env k r src =
    let t = reg_type r in
    let* l, li = Cv.Abi.load t (`var src) in
    let+ callai, callar, callam = match dec r with
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy t, `var l) in
        k.callai @! [li; i],
        Ftree.snoc k.callar r,
        k.callam
      | None ->
        let callai = Ftree.snoc k.callai li in
        let callam = Ftree.snoc k.callam (`var l) in
        !!(callai, k.callar, callam) in
    {k with callai; callar; callam}

  (* A compound argument to a call passed in two registers. *)
  let tworeg_arg ~dec env k r1 r2 src =
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let ok1 = dec r1 in
    let ok2 = dec r2 in
    let* o, oi = Cv.Abi.binop (`add `i64) (`var src) o8 in
    let* l1, li1 = Cv.Abi.load `i64 (`var src) in
    let* l2, li2 = Cv.Abi.load `i64 (`var o) in
    let+ callai, callar, callam = match ok1, ok2 with
      | Some r1, Some r2 ->
        let* i1 = Cv.Abi.insn @@ `uop (`reg r1, `copy t1, `var l1) in
        let+ i2 = Cv.Abi.insn @@ `uop (`reg r2, `copy t2, `var l2) in
        k.callai @! [oi; li1; li2; i1; i2],
        k.callar @! [r1; r2],
        k.callam
      | Some r1, None ->
        let+ i1 = Cv.Abi.insn @@ `uop (`reg r1, `copy t1, `var l1) in
        k.callai @! [oi; li1; li2; i1],
        Ftree.snoc k.callar r1,
        Ftree.snoc k.callam (`var l2)
      | None, Some r2 ->
        let+ i2 = Cv.Abi.insn @@ `uop (`reg r2, `copy t2, `var l2) in
        k.callai @! [oi; li1; li2; i2],
        Ftree.snoc k.callar r2,
        Ftree.snoc k.callam (`var l1)
      | None, None ->
        let callai = k.callai @! [oi; li1; li2] in
        let callam = k.callam @! [`var l1; `var l2] in
        !!(callai, k.callar, callam) in
    {k with callai; callar; callam}

  (* A compound argument to a call passed in memory. *)
  let memory_arg env k size src =
    let+ ldm = Cv.Abi.ldm `i64 src size in
    let callai, callam =
      List.fold ldm ~init:(k.callai, k.callam) ~f:(fun (ai, am) i ->
          let ai = Ftree.snoc ai i in
          let am = match Abi.Insn.op i with
            | `load (x, _, _) ->
              Ftree.snoc am (x :> Abi.operand)
            | _ -> am in
          ai, am) in
    {k with callai; callam}

  let call_ret_basic x t k =
    let r, t = match (t : Type.ret) with
      | #Type.fp as f -> sse_rets.(0), f
      | #Type.imm as m -> int_rets.(0), m
      | `si8 -> int_rets.(0), `i8
      | `si16 -> int_rets.(0), `i16
      | `si32 -> int_rets.(0), `i32
      | `name _ -> assert false in
    let+ i = Cv.Abi.insn @@ `uop (`var x, `copy t, `reg r) in
    let callri = Ftree.snoc k.callri i in
    {k with callri; callrr = [r]}

  (* Fits in one register. *)
  let call_ret_onereg env x r lk k =
    let x = find_ref env x in
    let t = reg_type r in
    let reg = match t with
      | `i64 -> int_rets.(0)
      | `f64 -> sse_rets.(0) in
    let+ st = Cv.Abi.store t (`reg reg) (`var x) in
    let callri = Ftree.snoc k.callri st in
    {k with callri; callrr = [reg]}

  (* Fits in two registers. *)
  let call_ret_tworeg env x r1 r2 lk k =
    let x = find_ref env x in
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let reg1, reg2 = match t1, t2 with
      | `i64, `i64 -> int_rets.(0), int_rets.(1)
      | `i64, `f64 -> int_rets.(0), sse_rets.(0)
      | `f64, `i64 -> sse_rets.(0), int_rets.(0)
      | `f64, `f64 -> sse_rets.(0), sse_rets.(1) in
    let* o, oi = Cv.Abi.binop (`add `i64) (`var x) o8 in
    let* st1 = Cv.Abi.store t1 (`reg reg1) (`var x) in
    let+ st2 = Cv.Abi.store t2 (`reg reg2) (`var o) in
    let callri = k.callri @! [oi; st1; st2] in
    {k with callri; callrr = [reg1; reg2]}

  (* Passed as a reference to memory. We need to allocate
     a new stack slot for this one. *)
  let call_ret_memory env x lk k =
    let r = int_args.(0) in
    let* y = new_slot env lk.size lk.align in
    let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy `i64, `var y) in
    let callai = Ftree.snoc k.callai i in
    let callar = Ftree.cons k.callar r in
    Hashtbl.set env.refs ~key:x ~data:y;
    {k with callai; callar; callrr = [int_rets.(0)]}

  (* Handle the compound type return value of a call.  *)
  let lower_call_ret env kret k = match kret with
    | `none -> !!k
    | `basic (x, t) -> call_ret_basic x t k
    | `compound (x, lk) -> match lk.cls with
      | Kreg _ when lk.size = 0 -> !!k
      | Kreg (r, _) when lk.size = 8 -> call_ret_onereg env x r lk k
      | Kreg (r1, r2) -> call_ret_tworeg env x r1 r2 lk k
      | Kmem -> call_ret_memory env x lk k

  let expect_arg_var env l : operand -> Var.t Context.t = function
    | `var x -> !!x
    | x ->
      Context.failf
        "Expected var for `call` operand in block %a \
         of function $%s, got %a" Label.pp l
        (Func.name env.fn) pp_operand x ()

  (* Figure out how we should pass the argument `a` at the call site. *)
  let classify_call_arg ~dec ~ni ~ns env key k a =
    typeof_operand env a >>= function
    | #Type.imm when !ni < 1 ->
      (* Ran out of integer registers. *)
      !!{k with callam = Ftree.snoc k.callam (oper a)}
    | #Type.fp when !ns < 1 ->
      (* Ran out of SSE registers. *)
      !!{k with callam = Ftree.snoc k.callam (oper a)}
    | #Type.imm as m ->
      (* Use an integer register. *)
      let r = int_args.(num_int_args - !ni) in
      let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy m, oper a) in
      let callai = Ftree.snoc k.callai i in
      let callar = Ftree.snoc k.callar r in
      decr ni; {k with callai; callar}
    | #Type.fp as f ->
      (* Use an SSE register. *)
      let r = sse_args.(num_sse_args - !ns) in
      let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy f, oper a) in
      let callai = Ftree.snoc k.callai i in
      let callar = Ftree.snoc k.callar r in
      decr ns; {k with callai; callar}
    | `flag -> assert false
    | `compound (s, _, _) | `opaque (s, _, _) ->
      (* Figure out what class this type is. *)
      let*? lt = Typecheck.Env.layout s env.tenv in
      let* x = expect_arg_var env key a in
      let lk = classify_layout lt in
      let src = find_ref env x in
      match lk.cls with
      | Kreg _ when lk.size = 0 -> !!k
      | Kreg (r, _) when lk.size = 8 -> onereg_arg ~dec env k r src
      | Kreg (r1, r2) -> tworeg_arg ~dec env k r1 r2 src
      | Kmem -> memory_arg env k lk.size (`var src)

  (* Lower the `call` instructions. *)
  let lower env = iter_blks env ~f:(fun b ->
      Blk.insns b |> Context.Seq.iter ~f:(fun i ->
          match Insn.op i with
          | `call (ret, _, args, vargs) ->
            let key = Insn.label i in
            (* See if we're returning a compound type. *)
            let* kret = match ret with
              | Some (x, `name n) ->
                let*? lt = Typecheck.Env.layout n env.tenv in
                !!(`compound (x, classify_layout lt))
              | Some (x, t) -> !!(`basic (x, t))
              | None -> !!`none in
            (* Counters for the number of integer and SSE registers
               remaining, before arguments are passed in memory. *)
            let ni = ref @@ match kret with
              | `compound (_, {cls = Kmem; _}) -> num_int_args - 1
              | _ -> num_int_args in
            let ns = ref num_sse_args in
            (* Decrement the counter based on the arg class. *)
            let dec = function
              | Rint | Rnone when !ni < 1 -> None
              | Rsse when !ns < 1 -> None
              | Rint | Rnone ->
                let r = int_args.(num_int_args - !ni) in
                decr ni;
                Some r
              | Rsse ->
                let r = sse_args.(num_sse_args - !ns) in
                decr ns;
                Some r in
            (* Process each argument. *)
            let acls = classify_call_arg ~dec ~ni ~ns env key in
            let* k = Context.List.fold args ~init:empty_call ~f:acls in
            let* k = Context.List.fold vargs ~init:k ~f:acls in
            (* Process the return value. *)
            let+ k = lower_call_ret env kret k in
            Hashtbl.set env.calls ~key ~data:k
          | _ -> !!()))
end

module Lower = struct
  let map_var env x =
    match Hashtbl.find env.canon_ref x with
    | Some y -> y
    | None -> match Hashtbl.find env.refs x with
      | Some y -> y
      | None -> x

  let map_operand env : operand -> Abi.operand = function
    | `var x -> `var (map_var env x)
    | o -> oper o

  let map_local env : local -> Abi.local = function
    | `label (l, args) ->
      `label (l, List.map args ~f:(map_operand env))

  let map_global env : global -> Abi.global = function
    | `var x -> `var (`var (map_var env x))
    | (`addr _ | `sym _) as g -> g

  let map_dst env : dst -> Abi.dst = function
    | #local as l -> (map_local env l :> Abi.dst)
    | #global as g -> (map_global env g :> Abi.dst)

  let map_basic env (b : Insn.basic) : Abi.Insn.basic =
    let op = map_operand env in
    match b with
    | `bop (x, b, l, r) -> `bop (`var x, b, op l, op r)
    | `uop (x, u, a) -> `uop (`var x, u, op a)
    | `sel (x, t, c, l, r) -> `sel (`var x, t, `var c, op l, op r)

  let map_mem env (m : Insn.mem) : Abi.Insn.mem =
    let op = map_operand env in
    match m with
    | `load (x, t, a) -> `load (`var x, t, op a)
    | `store (t, v, a) -> `store (t, op v, op a)

  let map_call env l f =
    let k = Hashtbl.find_exn env.calls l in
    let pre = Ftree.to_list k.callai in
    let rargs =
      Ftree.to_list k.callar |>
      List.map ~f:(fun r -> `reg r) in
    let margs = Ftree.to_list k.callam in
    let post = Ftree.to_list k.callri in
    let c = `call (k.callrr, map_global env f, rargs @ margs) in
    pre @ (Abi.Insn.create ~label:l c :: post)

  let map_compound env (c : Insn.compound) = match c with
    | `ref _ -> []
    | `unref (x, _, _) ->
      Hashtbl.find env.unrefs x |>
      Option.value ~default:[]

  let map_insn env i =
    let l = Insn.label i in
    let ins = Abi.Insn.create ~label:l in
    match Insn.op i with
    | #Insn.basic as b -> [ins (map_basic env b :> Abi.Insn.op)]
    | #Insn.mem as m -> [ins (map_mem env m :> Abi.Insn.op)]
    | #Insn.compound as c -> map_compound env c
    | #Insn.variadic -> failwith "unimplemented"
    | `call (_, f, _, _) -> map_call env l f

  let map_ctrl env l (c : ctrl) : Abi.insn list * Abi.ctrl =
    let dst = map_dst env in
    let loc = map_local env in
    match c with
    | `hlt -> [], `hlt
    | `jmp d -> [], `jmp (dst d)
    | `br (c, y, n) -> [], `br (`var (map_var env c), dst y, dst n)
    | `sw (t, i, d, tbl) ->
      let i = match i with
        | `var x -> `var (`var (map_var env x))
        | `sym s -> `sym s in
      let d = loc d in
      let tbl =
        Ctrl.Table.enum tbl |>
        Seq.map ~f:(fun (v, l) -> v, loc l) |>
        Seq.to_list |> fun l ->
        Abi.Ctrl.Table.create_exn l t in
      [], `sw(t, i, d, tbl)
    | `ret None -> [], `ret []
    | `ret Some _ ->
      let r = Hashtbl.find_exn env.rets l in
      r.reti, `ret r.retr

  let map_blks env =
    let entry = Func.entry env.fn in
    Func.blks env.fn |> Seq.map ~f:(fun b ->
        let l = Blk.label b in
        let pins =
          if Label.(l = entry) then
            Vec.to_sequence_mutable env.params |>
            Seq.map ~f:(fun p -> p.pins) |>
            Seq.to_list |> List.concat
          else [] in
        let ins =
          Blk.insns b |> Seq.map ~f:(map_insn env) |>
          Seq.to_list |> List.concat in
        let cins, ctrl = map_ctrl env l @@ Blk.ctrl b in
        let args = Blk.args b |> Seq.to_list in
        Abi.Blk.create () ~args ~ctrl
          ~label:l ~insns:(pins @ ins @ cins)) |>
    Seq.to_list

  let lower env =
    let slots = Func.slots env.fn |> Seq.to_list in
    let slots = slots @ Vec.to_list env.slots in
    let args =
      Vec.to_sequence_mutable env.params |>
      Seq.map ~f:(fun p -> p.pvar, p.pty) |>
      Seq.to_list in
    let blks = map_blks env in
    let lnk = Func.linkage env.fn in
    let dict = Dict.(set empty Func.Tag.linkage lnk) in
    Abi.Func.create () ~dict ~slots ~args ~blks
      ~name:(Func.name env.fn)
end

let run tenv fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let env = init_env tenv fn in
    let* () = Params.lower env in
    let* () = Refs.canonicalize env in
    let* () = Rets.lower env in
    let* () = Calls.lower env in
    let*? fn = Lower.lower env in
    !!fn
  else
    Context.failf
      "In Lower_abi: expected SSA form for function $%s"
      (Func.name fn) ()

