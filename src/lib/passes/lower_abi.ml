(* Lower a function according to the System V ABI (AMD64). *)

open Core
open Regular.Std
open Virtual

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

type env = {
  fn           : func;
  tenv         : Typecheck.env;
  rets         : (Abi.insn list * Abi.ctrl) Label.Table.t;
  refs         : Var.t Var.Table.t;
  slots        : slot Vec.t;
  mutable rmem : Var.t option;
}

let init_env tenv fn = {
  fn;
  tenv;
  rets = Label.Table.create ();
  refs = Var.Table.create ();
  slots = Vec.create ();
  rmem = None;
}

let make_rmem env = match env.rmem with
  | Some dst -> !!dst
  | None ->
    let+ dst = Context.Var.fresh in
    env.rmem <- Some dst;
    dst

let oper (o : operand) = (o :> Abi.operand)

let find_ref env x = match Hashtbl.find env.refs x with
  | Some y -> !!y
  | None ->
    Context.failf "Missing ref for var %a in function $%s"
      Var.pp x (Func.name env.fn) ()

let expect_ret_var env l : operand -> Var.t Context.t = function
  | `var x -> !!x
  | x ->
    Context.failf
      "Expected var for return operand in block %a of \
       function $%s, got %a"
      Label.pp l (Func.name env.fn) pp_operand x ()

let selret env =
  let go f =
    Func.blks env.fn |> Context.Seq.iter ~f:(fun b ->
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
    let+ r = Context.Virtual.Abi.insn @@ `uop (`reg reg, u, oper x) in
    Hashtbl.set env.rets ~key ~data:([r], `ret [reg])
  | Some (`si8 | `si16 | `si32) -> go @@ fun key x ->
    (* Return in the first integer register, with a sign extension. *)
    let reg = int_rets.(0) in
    let+ r = Context.Virtual.Abi.insn @@ `uop (`reg reg, `sext `i64, oper x) in
    Hashtbl.set env.rets ~key ~data:([r], `ret [reg])
  | Some (#Type.fp as t) -> go @@ fun key x ->
    (* Return in the first floating point register. *)
    let reg = sse_rets.(0) in
    let+ r = Context.Virtual.Abi.insn @@ `uop (`reg reg, `copy t, oper x) in
    Hashtbl.set env.rets ~key ~data:([r], `ret [reg])
  | Some `name n ->
    let*? lt = Typecheck.Env.layout n env.tenv in
    let k = classify_layout lt in
    match k.cls with
    | Kreg _ when k.size = 0 -> go @@ fun key _ ->
      (* Struct is empty, so we return nothing. *)
      !!(Hashtbl.set env.rets ~key ~data:([], `ret []))
    | Kreg (r, _) when k.size = 8 -> go @@ fun key x ->
      (* Struct is returned in a single register. *)
      let* x = expect_ret_var env key x in
      let* x = find_ref env x in
      let t = reg_type r in
      let reg = match t with
        | `i64 -> int_rets.(0)
        | `f64 -> sse_rets.(0) in
      let+ r = Context.Virtual.Abi.insn @@ `load (`reg reg, t, `var x) in
      Hashtbl.set env.rets ~key ~data:([r], `ret [reg])
    | Kreg (r1, r2) -> go @@ fun key x ->
      (* Struct is returned in two registers of varying classes. *)
      let* x = expect_ret_var env key x in
      let* x = find_ref env x in
      let t1 = reg_type r1 in
      let t2 = reg_type r2 in
      let ni = ref 0 in
      let ns = ref 0 in
      let reg1 = match t1 with
        | `i64 -> incr ni; int_rets.(0)
        | `f64 -> incr ns; sse_rets.(0) in
      let reg2 = match t2 with
        | `i64 -> int_rets.(!ni)
        | `f64 -> sse_rets.(!ns) in
      let* ld1 = Context.Virtual.Abi.insn @@ `load (`reg reg1, `i64, `var x) in
      let o = `int (Bv.M64.int 8, `i64) in
      let* a, add = Context.Virtual.Abi.binop (`add `i64) (`var x) o in
      let+ ld2 = Context.Virtual.Abi.insn @@ `load (`reg reg2, `i64, `var a) in
      Hashtbl.set env.rets ~key ~data:([ld1; add; ld2], `ret [reg1; reg2])
    | Kmem -> go @@ fun key x ->
      (* Struct is blitted to a pointer held by by the implicit
         first argument of the function. This pointer becomes the
         return value. *)
      let* x = expect_ret_var env key x in
      let* src = find_ref env x in
      let* dst = make_rmem env in
      let* blit = Context.Virtual.Abi.blit
          `i64 k.size ~src:(`var src) ~dst:(`var dst) in
      let reg = int_rets.(0) in
      let cpy = `uop (`reg reg, `copy `i64, `var dst) in
      let+ r = Context.Virtual.Abi.insn cpy in
      Hashtbl.set env.rets ~key ~data:(blit @ [r], `ret [reg])

let run tenv fn =
  let env = init_env tenv fn in
  let* () = selret env in
  failwith "unimplemented"
