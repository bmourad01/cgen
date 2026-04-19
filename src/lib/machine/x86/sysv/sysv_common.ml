open Core
open Regular.Std
open Virtual

module LT = Label.Dense_table
module VT = Var.Dense_table
module LS = Label.Dense_set

let reg_str = Format.asprintf "%a" X86_amd64_common.Reg.pp

let int_args = Array.map ~f:reg_str [|
    `rdi;
    `rsi;
    `rdx;
    `rcx;
    `r8;
    `r9;
  |]

let int_arg_queue () =
  let q = Stack.create () in
  for i = Array.length int_args - 1 downto 0 do
    Stack.push q int_args.(i)
  done;
  q

let int_rets = Array.map ~f:reg_str [|
    `rax;
    `rdx;
  |]

let sse_args = Array.map ~f:reg_str [|
    `xmm0;
    `xmm1;
    `xmm2;
    `xmm3;
    `xmm4;
    `xmm5;
    `xmm6;
    `xmm7;
  |]

let sse_arg_queue () =
  let q = Stack.create () in
  for i = Array.length sse_args - 1 downto 0 do
    Stack.push q sse_args.(i)
  done;
  q

let sse_rets = Array.map ~f:reg_str [|
    `xmm0;
    `xmm1;
  |]

type reg =
  | Rnone
  | Rint
  | Rsse
[@@deriving equal]

let reg_type = function
  | Rnone -> assert false
  | Rint -> `i64
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

let rec classify_member ~gamma ds =
  Seq.fold_until ds
    ~init:(Rnone, Rnone, 0)
    ~finish:(fun (r1, r2, _) -> Some (r1, r2))
    ~f:(fun (r1, r2, s) -> function
        | #Type.imm as m ->
          let s' = s + (Type.sizeof_imm m / 8) in
          let r1', r2' = match s / 8 with
            | 0 -> Rint, r2
            | 1 -> r1, Rint
            | _ -> assert false in
          Continue (r1', r2', s')
        | #Type.fp as f ->
          let s' = s + (Type.sizeof_fp f / 8) in
          let r1', r2' = match s / 8 with
            | 0 -> merge_reg r1 Rsse, r2
            | 1 -> r1, merge_reg r2 Rsse
            | _ -> assert false in
          Continue (r1', r2', s')
        | `pad n -> Continue (r1, r2, s + n)
        | `opaque _ -> Stop None
        | `union (name, n) ->
          match classify_union ~gamma (gamma name) with
          | None -> Stop None
          | Some (ur1, ur2) ->
            let r1 = match s / 8 with
              | 0 -> merge_reg r1 ur1
              | 1 -> r1
              | _ -> assert false in
            let r2 = match (s + n - 1) / 8 with
              | 0 -> r2
              | 1 -> merge_reg r2 ur2
              | _ -> assert false in
            Continue (r1, r2, s + n))

and classify_union ~gamma dss =
  Seq.fold_until dss
    ~init:(Rnone, Rnone)
    ~finish:Option.some
    ~f:(fun (r1, r2) ds ->
        match classify_member ~gamma ds with
        | None -> Stop None
        | Some (mr1, mr2) ->
          let r1' = merge_reg r1 mr1 in
          let r2' = merge_reg r2 mr2 in
          Continue (r1', r2'))

let classify_layout ~gamma lt =
  let size = Type.Layout.sizeof lt in
  (* Align to the nearest eightbyte boundary. *)
  let align = max 8 @@ Type.Layout.align lt in
  let size = (size + align - 1) land -align in
  let cls =
    (* Try to pack the type into two registers. If it is
       larger than 16 bytes or contains unaligned fields
       then it will be passed on the stack. Note that a
       type with an empty size is also passed in memory. *)
    if size > 0 && size <= 16 then
      Type.Layout.members lt |> Either.value_map
        ~first:(classify_member ~gamma)
        ~second:(classify_union ~gamma) |>
      Option.value_map ~default:Kmem
        ~f:(fun (r1, r2) -> Kreg (r1, r2))
    else Kmem in
  {size; align; cls}

type ret = {
  reti : Abi.insn list;           (* Copy the data to be returned. *)
  retr : (string * operand) list; (* Registers to return in. *)
}

let empty_ret = {
  reti = [];
  retr = [];
}

type callret = Var.t * Type.basic * string

type call = {
  callai : Abi.insn Ftree.t;         (* Set up the arguments before the call. *)
  callar : Abi.Insn.callarg Ftree.t; (* Passing arguments. *)
  callri : Abi.insn Ftree.t;         (* Copy the return value after the call. *)
  callrr : callret list;             (* Registers holding the return value. *)
}

let empty_call = {
  callai = Ftree.empty;
  callar = Ftree.empty;
  callri = Ftree.empty;
  callrr = [];
}

let (@>*) t l = List.fold l ~init:t ~f:Ftree.snoc
let (@>) t x = Ftree.snoc t x
let (<@) x t = Ftree.cons t x

type param = {
  pty  : Type.basic;
  pvar : Abi.Func.arg;
  pins : Abi.insn list;
}

(* Register save area for variadic functions.

   Bytes [0, 48) contains the integer registers.
   Bytes [48, 176) contains the SSE registers.
*)
type regsave = {
  rsslot : Var.t;
  rsint  : Abi.blk;
  rssse  : Abi.blk;
}

type vaarg = {
  vablks : Abi.blk list; (* `va_arg` logic, in topological order. *)
  vacont : Label.t;      (* Continuation block. *)
}

type env = {
  fn            : func;                (* The original function. *)
  blks          : blk Label.Tree.t;    (* Map of basic blocks. *)
  tenv          : Typecheck.env;       (* Typing environment. *)
  rets          : ret LT.t;            (* Lowered `ret` instructions. *)
  calls         : call LT.t;           (* Lowered `call` instructions. *)
  tailcalls     : LS.t;                (* Labels of tail-call-eligible calls. *)
  refs          : Var.t VT.t;          (* Struct var to its slot. *)
  unrefs        : Abi.insn list VT.t;  (* `unref` to blit. *)
  blits         : Abi.insn list LT.t;  (* Stores of structs. *)
  slots         : slot Vec.t;          (* New stack slots. *)
  params        : param Vec.t;         (* Function parameters. *)
  layout        : acls String.Table.t; (* Cached struct layouts. *)
  vastart       : Abi.insn list LT.t;  (* Lowered `vastart` instructions. *)
  vaarg         : vaarg LT.t;          (* Lowered `vaarg` instructions. *)
  mutable rsave : regsave option;      (* Register save area. *)
  mutable rmem  : Var.t option;        (* Return value blitted to memory. *)
  mutable alpar : Var.t option;        (* Implicit AL argument. *)
}

(* For simplicity, let's make sure each existing stack slot is aligned
   by at least an eight-byte boundary, and that their sizes are divisible
   by eight as well. *)
let align_slots fn =
  let ss = Func.slots fn |> Seq.to_list in
  let fn = List.fold ss ~init:fn ~f:(fun fn s ->
      Func.remove_slot fn @@ Slot.var s) in
  List.map ss ~f:(fun s ->
      let x = Slot.var s in
      let align = max 8 @@ Slot.align s in
      let size = (Slot.size s + 8 - 1) land -8 in
      Virtual.Slot.create_exn x ~size ~align) |>
  List.fold ~init:fn ~f:Virtual.Func.insert_slot

let init_env tenv fn =
  let fn = align_slots fn in {
    fn;
    blks = Func.map_of_blks fn;
    tenv;
    rets = LT.create ();
    calls = LT.create ();
    tailcalls = LS.create ();
    refs = VT.create ();
    unrefs = VT.create ();
    blits = LT.create ();
    slots = Vec.create ();
    params = Vec.create ();
    layout = String.Table.create ();
    vastart = LT.create ();
    vaarg = LT.create ();
    rsave = None;
    rmem = None;
    alpar = None;
  }

module Make0(Context : Context_intf.S) = struct
  open Context.Syntax

  let new_slot env size align =
    let* x = Context.Var.fresh in
    let+? s = Slot.create x ~size ~align in
    Vec.push env.slots s;
    x

  let find_ref env x = match VT.find env.refs x with
    | Some y -> y
    | None ->
      failwithf "%a has no ref in function $%s"
        Var.pps x (Func.name env.fn) ()

  let resolve_union env name =
    match Typecheck.Env.layout name env.tenv with
    | Error _ -> Seq.empty
    | Ok lt -> match Type.Layout.members lt with
      | Second dss -> dss
      | First _ -> Seq.empty

  let type_cls env s = match Hashtbl.find env.layout s with
    | Some k -> !!k
    | None ->
      let+? lt = Typecheck.Env.layout s env.tenv in
      let k = classify_layout ~gamma:(resolve_union env) lt in
      Hashtbl.set env.layout ~key:s ~data:k;
      k

  let i8 i = `int (Bv.M8.int i, `i8)
  let i32 i = `int (Bv.M32.int i, `i32)
  let i64 i = `int (Bv.M64.int i, `i64)

  let typeof_var env x =
    Context.lift_err ~prefix:"Sysv" @@
    Typecheck.Env.typeof_var env.fn x env.tenv

  let word env = (Target.word (Typecheck.Env.target env.tenv) :> Type.t)

  let typeof_operand env : operand -> Type.t Context.t = function
    | `int (_, t) -> !!(t :> Type.t)
    | `bool _ -> !!`flag
    | `float _ -> !!`f32
    | `double _ -> !!`f64
    | `sym _ -> !!(word env)
    | `var x -> typeof_var env x
end
