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
  fn   : func;
  tenv : Typecheck.env;
  rets : (Abi.insn list * Abi.ctrl) Label.Table.t;
}

let oper (o : operand) = (o :> Abi.operand)


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
    let reg = int_rets.(0) in
    let u = match t with
      | `i8 | `i16 | `i32 -> `zext `i64
      | `i64 -> `copy `i64 in
    let cpy = `uop (`reg reg, u, oper x) in
    let+ r = Context.Virtual.Abi.insn cpy in
    Hashtbl.set env.rets ~key ~data:([r], `ret [reg])
  | Some (`si8 | `si16 | `si32) -> go @@ fun key x ->
    let reg = int_rets.(0) in
    let cpy = `uop (`reg reg, `sext `i64, oper x) in
    let+ r = Context.Virtual.Abi.insn cpy in
    Hashtbl.set env.rets ~key ~data:([r], `ret [reg])
  | Some (#Type.fp as t) -> go @@ fun key x ->
    let reg = sse_rets.(0) in
    let cpy = `uop (`reg reg, `copy t, oper x) in
    let+ r = Context.Virtual.Abi.insn cpy in
    Hashtbl.set env.rets ~key ~data:([r], `ret [reg])
  | Some `name _n ->
    !!()

let run _tenv _fn = failwith "unimplemented"
