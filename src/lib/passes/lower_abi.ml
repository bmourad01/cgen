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
  callar : Abi.operand Ftree.t; (* Passing register arguments. *)
  callam : Abi.operand Ftree.t; (* Passing memory arguments. *)
  callri : Abi.insn Ftree.t;    (* Copy the return value after the call. *)
  callrs : string list;         (* Registers holding the return value. *)
}

let empty_call = {
  callai = Ftree.empty;
  callar = Ftree.empty;
  callam = Ftree.empty;
  callri = Ftree.empty;
  callrs = [];
}

let (@!) t l = Ftree.(append t @@ of_list l)

type env = {
  fn           : func;               (* The original function. *)
  blks         : blk Label.Tree.t;   (* Map of basic blocks. *)
  cfg          : Cfg.t;              (* Control-flow graph. *)
  doms         : Label.t tree;       (* Dominator tree. *)
  tenv         : Typecheck.env;      (* Typing environment. *)
  rets         : ret Label.Table.t;  (* Lowered `ret` instructions. *)
  calls        : call Label.Table.t; (* Lowered `call` instructions. *)
  refs         : Var.t Var.Table.t;  (* `unref` to `ref` *)
  slots        : slot Vec.t;         (* New stack slots. *)
  mutable rmem : Var.t option;       (* Return value blitted to memory. *)
}

let init_env tenv fn =
  let blks = Func.map_of_blks fn in
  let cfg = Cfg.create fn in
  let doms = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  let rets = Label.Table.create () in
  let calls = Label.Table.create () in
  let refs = Var.Table.create () in
  let slots = Vec.create () in
  {fn; blks; cfg; doms; tenv; rets; calls; refs; slots; rmem = None}

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

let make_rmem env = match env.rmem with
  | Some dst -> !!dst
  | None ->
    let+ dst = Context.Var.fresh in
    env.rmem <- Some dst;
    dst

let find_ref env x = match Hashtbl.find env.refs x with
  | Some y -> !!y
  | None ->
    Context.failf "Missing ref for var %a in function $%s"
      Var.pp x (Func.name env.fn) ()

let o8 = `int (Bv.M64.int 8, `i64)

let oper (o : operand) = (o :> Abi.operand)

let typeof_var tenv fn x =
  Context.lift_err @@ Typecheck.Env.typeof_var fn x tenv

let word tenv = (Target.word (Typecheck.Env.target tenv) :> Type.t)

let typeof_operand tenv fn : operand -> Type.t Context.t = function
  | `int (_, t) -> !!(t :> Type.t)
  | `bool _ -> !!`flag
  | `float _ -> !!`f32
  | `double _ -> !!`f64
  | `sym _ -> !!(word tenv)
  | `var x -> typeof_var tenv fn x

module Rets = struct
  let expect_ret_var env l : operand -> Var.t Context.t = function
    | `var x -> !!x
    | x ->
      Context.failf
        "Expected var for `ret` operand in block %a \
         of function $%s, got %a" Label.pp l
        (Func.name env.fn) pp_operand x ()

  (* Lower the `ret` instructions. *)
  let lower env =
    let go f = iter_blks env ~f:(fun b ->
        let key = Blk.label b in
        match Blk.ctrl b with
        | `ret Some x -> f key x
        | `ret None ->
          Context.failf
            "Expected return value in block %a of function $%s"
            Label.pp key (Func.name env.fn) ()
        | _ -> !!()) in
    match Func.return env.fn with
    | None -> !!()
    | Some (#Type.imm as t) -> go @@ fun key x ->
      (* Return in the first integer register. *)
      let reg = int_rets.(0) in
      let u = match t with
        | `i8 | `i16 | `i32 -> `zext `i64
        | `i64 -> `copy `i64 in
      let+ r = Cv.Abi.insn @@ `uop (`reg reg, u, oper x) in
      Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}
    | Some (`si8 | `si16 | `si32) -> go @@ fun key x ->
      (* Return in the first integer register, with a sign extension. *)
      let reg = int_rets.(0) in
      let+ r = Cv.Abi.insn @@ `uop (`reg reg, `sext `i64, oper x) in
      Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}
    | Some (#Type.fp as t) -> go @@ fun key x ->
      (* Return in the first floating point register. *)
      let reg = sse_rets.(0) in
      let+ r = Cv.Abi.insn @@ `uop (`reg reg, `copy t, oper x) in
      Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}
    | Some `name n ->
      let*? lt = Typecheck.Env.layout n env.tenv in
      let k = classify_layout lt in
      match k.cls with
      | Kreg _ when k.size = 0 -> go @@ fun key _ ->
        (* Struct is empty, so we return nothing. *)
        !!(Hashtbl.set env.rets ~key ~data:empty_ret)
      | Kreg (r, _) when k.size = 8 -> go @@ fun key x ->
        (* Struct is returned in a single register. *)
        let* x = expect_ret_var env key x in
        let* x = find_ref env x in
        let t = reg_type r in
        let reg = match t with
          | `i64 -> int_rets.(0)
          | `f64 -> sse_rets.(0) in
        let+ r = Cv.Abi.insn @@ `load (`reg reg, t, `var x) in
        Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}
      | Kreg (r1, r2) -> go @@ fun key x ->
        (* Struct is returned in two registers of varying classes. *)
        let* x = expect_ret_var env key x in
        let* x = find_ref env x in
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
      | Kmem -> go @@ fun key x ->
        (* Struct is blitted to a pointer held by by the implicit
           first argument of the function. This pointer becomes the
           return value. *)
        let* x = expect_ret_var env key x in
        let* src = find_ref env x in
        let* dst = make_rmem env in
        let* blit = Cv.Abi.blit `i64 k.size ~src:(`var src) ~dst:(`var dst) in
        let reg = int_rets.(0) in
        let+ r = Cv.Abi.insn @@ `uop (`reg reg, `copy `i64, `var dst) in
        Hashtbl.set env.rets ~key ~data:{
          reti = blit @ [r];
          retr = [reg]
        }
end

module Calls = struct
  (* A compound argument to a call passed in a single register. *)
  let onereg_arg ~dec env k r src =
    let+ l, li = Cv.Abi.load `i64 (`var src) in
    let callai = Ftree.snoc k.callai li in
    let callar, callam = match dec r with
      | true -> Ftree.snoc k.callar (`var l), k.callam
      | false -> k.callar, Ftree.snoc k.callam (`var l) in
    {k with callai; callar; callam}

  (* A compound argument to a call passed in two registers. *)
  let tworeg_arg ~dec env k r1 r2 src =
    let ok1 = dec r1 in
    let ok2 = dec r2 in
    let* o, oi = Cv.Abi.binop (`add `i64) (`var src) o8 in
    let* l1, li1 = Cv.Abi.load `i64 (`var src) in
    let+ l2, li2 = Cv.Abi.load `i64 (`var o) in
    let callai = k.callai @! [oi; li1; li2] in
    let callar, callam = match ok1, ok2 with
      | true, true ->
        k.callar @! [`var l1; `var l2],
        k.callam
      | true, false ->
        Ftree.snoc k.callar (`var l1),
        Ftree.snoc k.callam (`var l2)
      | false, true ->
        Ftree.snoc k.callar (`var l2),
        Ftree.snoc k.callam (`var l1)
      | false, false ->
        k.callar,
        k.callam @! [`var l1; `var l2] in
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

  (* Handle the compound type return value of a call.  *)
  let lower_call_ret_compound env kret k = match kret with
    | None -> !!k
    | Some (x, lk) -> match lk.cls with
      | Kreg _ when lk.size = 0 -> !!k
      | Kreg (r, _) when lk.size = 8 ->
        (* Fits in one register. *)
        let* x = find_ref env x in
        let t = reg_type r in
        let reg = match t with
          | `i64 -> int_rets.(0)
          | `f64 -> sse_rets.(0) in
        let+ st = Cv.Abi.store t (`reg reg) (`var x) in
        let callri = Ftree.snoc k.callri st in
        {k with callri; callrs = [reg]}
      | Kreg (r1, r2) ->
        (* Fits in two registers. *)
        let* x = find_ref env x in
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
        {k with callri; callrs = [reg1; reg2]}
      | Kmem ->
        (* Passed as a reference to memory. We need to allocate
           a new stack slot for this one. *)
        let+ y = new_slot env lk.size lk.align in
        let callar = Ftree.cons k.callar (`var y) in
        Hashtbl.set env.refs ~key:x ~data:y;
        {k with callar; callrs = [int_rets.(0)]}

  let expect_arg_var env l : operand -> Var.t Context.t = function
    | `var x -> !!x
    | x ->
      Context.failf
        "Expected var for `call` operand in block %a \
         of function $%s, got %a" Label.pp l
        (Func.name env.fn) pp_operand x ()

  (* Figure out how we should pass the argument `a` at the call site. *)
  let classify_call_arg ~dec ~ni ~ns env key k a =
    typeof_operand env.tenv env.fn a >>= function
    | #Type.imm when !ni < 1 ->
      (* Ran out of integer registers. *)
      !!{k with callam = Ftree.snoc k.callam (oper a)}
    | #Type.fp when !ns < 1 ->
      (* Ran out of SSE registers. *)
      !!{k with callam = Ftree.snoc k.callam (oper a)}
    | #Type.imm ->
      (* Use an integer register. *)
      decr ni; !!{k with callar = Ftree.snoc k.callar (oper a)}
    | #Type.fp ->
      (* Use an SSE register. *)
      decr ns; !!{k with callar = Ftree.snoc k.callar (oper a)}
    | `flag -> assert false
    | `compound (s, _, _) | `opaque (s, _, _) ->
      (* Figure out what class this type is. *)
      let*? lt = Typecheck.Env.layout s env.tenv in
      let* x = expect_arg_var env key a in
      let* src = find_ref env x in
      match classify_layout lt with
      | {cls = Kreg _; size = 0; _} -> !!k
      | {cls = Kreg (r, _); size = 8; _} -> onereg_arg ~dec env k r src
      | {cls = Kreg (r1, r2); _} -> tworeg_arg ~dec env k r1 r2 src
      | {cls = Kmem; size; _} -> memory_arg env k size @@ `var src

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
                !!(Some (x, classify_layout lt))
              | Some _ | None -> !!None in
            (* Counters for the number of integer and SSE registers
               remaining, before arguments are passed in memory. *)
            let ni = ref @@ match kret with
              | Some (_, {cls = Kmem; _}) -> num_int_args - 1
              | Some _ | None -> num_int_args in
            let ns = ref num_sse_args in
            (* Decrement the counter based on the arg class. *)
            let dec = function
              | Rint | Rnone when !ni < 1 -> false
              | Rint | Rnone -> decr ni; true
              | Rsse when !ns < 1 -> false
              | Rsse -> decr ns; true in
            (* Process each argument. *)
            let acls = classify_call_arg ~dec ~ni ~ns env key in
            let* k = Context.List.fold args ~init:empty_call ~f:acls in
            let* k = Context.List.fold vargs ~init:k ~f:acls in
            (* Process the return value. *)
            let+ k = lower_call_ret_compound env kret k in
            Hashtbl.set env.calls ~key ~data:k
          | _ -> !!()))
end

let run tenv fn =
  let env = init_env tenv fn in
  let* () = Rets.lower env in
  let* () = Calls.lower env in
  failwith "unimplemented"
