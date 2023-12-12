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

let int_arg_queue () =
  let q = Stack.create () in
  for i = num_int_args - 1 downto 0 do
    Stack.push q int_args.(i)
  done;
  q

let int_rets = [|
  "RAX";
  "RDX";
|]

(* XMM0, XMM1, ..., XMM7 *)
let num_sse_args = 8

let sse_args =
  Array.init num_sse_args ~f:(Format.sprintf "XMM%d")

let sse_arg_queue () =
  let q = Stack.create () in
  for i = num_sse_args - 1 downto 0 do
    Stack.push q sse_args.(i)
  done;
  q

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

let (@>*) t l = List.fold l ~init:t ~f:Ftree.snoc
let (@>) t x = Ftree.snoc t x
let (<@) x t = Ftree.cons t x

type param = {
  pty  : Type.basic;
  pvar : Abi.var;
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

let rsave_sse_ofs = 48

type vaarg = {
  vablks : Abi.blk list; (* `va_arg` logic, in topological order. *)
  vacont : Label.t;      (* Continuation block. *)
}

type env = {
  fn            : func;                        (* The original function. *)
  blks          : blk Label.Tree.t;            (* Map of basic blocks. *)
  doms          : Label.t tree;                (* Dominator tree. *)
  tenv          : Typecheck.env;               (* Typing environment. *)
  rets          : ret Label.Table.t;           (* Lowered `ret` instructions. *)
  calls         : call Label.Table.t;          (* Lowered `call` instructions. *)
  refs          : Var.t Var.Table.t;           (* Canonicalization of `ref`s *)
  unrefs        : Abi.insn list Var.Table.t;   (* `unref` to store. *)
  canon_ref     : Var.t Var.Table.t;           (* Canonicalize `ref`s. *)
  slots         : slot Vec.t;                  (* New stack slots. *)
  params        : param Vec.t;                 (* Function parameters. *)
  layout        : acls String.Table.t;         (* Cached struct layouts. *)
  vastart       : Abi.insn list Label.Table.t; (* Lowered `vastart` instructions. *)
  vaarg         : vaarg Label.Table.t;         (* Lowered `vaarg` instructions. *)
  mutable rsave : regsave option;              (* Register save area. *)
  mutable rmem  : Var.t option;                (* Return value blitted to memory. *)
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
    layout = String.Table.create ();
    vastart = Label.Table.create ();
    vaarg = Label.Table.create ();
    rsave = None;
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

let type_cls env s = match Hashtbl.find env.layout s with
  | Some k -> !!k
  | None ->
    let*? lt = Typecheck.Env.layout s env.tenv in
    let k = classify_layout lt in
    Hashtbl.set env.layout ~key:s ~data:k;
    !!k

(* Common offsets. *)
let o4 = `int (Bv.M64.int 4, `i64)
let o8 = `int (Bv.M64.int 8, `i64)
let o16 = `int (Bv.M64.int 16, `i64)

(* Helpers for constructing constants. *)
let i8 i = `int (Bv.M8.int i, `i8)
let i32 i = `int (Bv.M32.int i, `i32)
let i64 i = `int (Bv.M64.int i, `i64)

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
  (* Allocate a single register as a parameter or
     pass it on the stack. *)
  let alloc_onereg qi qs = function
    | #Type.imm -> Stack.pop qi
    | #Type.fp -> Stack.pop qs

  (* Allocate two registers as a parameter. Both
     must be available, or the argument is passed
     on the stack. *)
  let alloc_tworeg qi qs t1 t2 = match t1, t2 with
    | #Type.imm, #Type.imm ->
      if Stack.length qi >= 2 then
        let r1 = Stack.pop_exn qi in
        let r2 = Stack.pop_exn qi in
        Some (r1, r2)
      else None
    | #Type.fp, #Type.fp ->
      if Stack.length qs >= 2 then
        let r1 = Stack.pop_exn qs in
        let r2 = Stack.pop_exn qs in
        Some (r1, r2)
      else None
    | #Type.imm, #Type.fp ->
      if Stack.length qi >= 1
      && Stack.length qs >= 1 then
        let r1 = Stack.pop_exn qi in
        let r2 = Stack.pop_exn qs in
        Some (r1, r2)
      else None
    | #Type.fp, #Type.imm ->
      if Stack.length qs >= 1
      && Stack.length qi >= 1 then
        let r1 = Stack.pop_exn qs in
        let r2 = Stack.pop_exn qi in
        Some (r1, r2)
      else None

  let init_regs env =
    let qi = int_arg_queue () in
    let qs = sse_arg_queue () in
    let+ () = match Func.return env.fn with
      | Some (#Type.basic | `si8 | `si16 | `si32) | None -> !!()
      | Some `name n -> type_cls env n >>= function
        | {cls = Kmem; _} ->
          let r = int_args.(0) in
          let* x = Context.Var.fresh in
          let+ i = Cv.Abi.insn @@ `uop (`var x, `copy `i64, `reg r) in
          let p = {pty = `i64; pvar = `reg r; pins = [i]} in
          Vec.push env.params p;
          env.rmem <- Some x;
          ignore (Stack.pop_exn qi)
        | _ -> !!() in
    alloc_onereg qi qs,
    alloc_tworeg qi qs

  let basic_param ~reg env t x =
    let+ pvar, pins = match reg t with
      | None -> !!(`var x, [])
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`var x, `copy t, `reg r) in
        `reg r, [i] in
    Vec.push env.params @@ {pty = t; pvar; pins}

  (* Pass in a single register, so we can reuse `x`. *)
  let onereg_param ~reg env x y r =
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
  let tworeg_param ~reg2 env y r1 r2 =
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let* x1 = Context.Var.fresh in
    let* x2 = Context.Var.fresh in
    let* o, oi = Cv.Abi.binop (`add `i64) (`var y) o8 in
    let* st1 = Cv.Abi.store t1 (`var x1) (`var y) in
    let* st2 = Cv.Abi.store t1 (`var x2) (`var o) in
    let+ p1, p2 = match reg2 t1 t2 with
      | None ->
        let p1 = {pty = t1; pvar = `var x1; pins = [st1]} in
        let p2 = {pty = t2; pvar = `var x2; pins = [oi; st2]} in
        !!(p1, p2)
      | Some (r1, r2) ->
        let* i1 = Cv.Abi.insn @@ `uop (`var x1, `copy t1, `reg r1) in
        let+ i2 = Cv.Abi.insn @@ `uop (`var x2, `copy t2, `reg r2) in
        let p1 = {pty = t1; pvar = `reg r1; pins = [i1; st1]} in
        let p2 = {pty = t2; pvar = `reg r2; pins = [i2; oi; st2]} in
        p1, p2 in
    Vec.push env.params p1;
    Vec.push env.params p2

  (* Blit the structure to a stack slot. *)
  let memory_param env y size =
    Seq.init (size / 8) ~f:(fun i -> i * 8) |>
    Context.Seq.iter ~f:(fun o ->
        let* x = Context.Var.fresh in
        let+ pins =
          if o = 0 then
            let+ st = Cv.Abi.store `i64 (`var x) (`var y) in
            [st]
          else
            let* o, oi = Cv.Abi.binop (`add `i64) (`var y) (i64 o) in
            let+ st = Cv.Abi.store `i64 (`var x) (`var o) in
            [oi; st] in
        let p = {pty = `i64; pvar = `var x; pins} in
        Vec.push env.params p)

  (* Quoting from the System V document, section 3.5.7:

     "The prologue of a function taking a variable argument list
      and known to call the macro va_start is expected to save the
      argument registers to the register save area."
  *)
  let needs_register_save env =
    Func.variadic env.fn &&
    Func.blks env.fn |>
    Seq.exists ~f:(fun b ->
        Blk.insns b |>
        Seq.map ~f:Insn.op |>
        Seq.exists ~f:(function
            | `vastart _ -> true
            | _ -> false))

  let register_save_int env sse s =
    let* label = Context.Label.fresh in
    let* save =
      Array.to_list int_args |>
      List.mapi ~f:(fun i r -> i * 8, r) |>
      Context.List.map ~f:(fun (o, r) ->
          if o = 0 then
            let+ st = Cv.Abi.store `i64 (`reg r) (`var s) in
            [st]
          else
            let* o, oi = Cv.Abi.binop (`add `i64) (`var s) (i64 o) in
            let+ st = Cv.Abi.store `i64 (`reg r) (`var o) in
            [oi; st]) in
    let zero = `int (Bv.zero, `i8) in
    let+ z, zi = Cv.Abi.binop (`eq `i8) (`reg "RAX") zero in
    let entry = `label (Func.entry env.fn, []) in
    let sse = `label (sse, []) in
    Abi.Blk.create () ~label
      ~insns:(List.concat save @ [zi])
      ~ctrl:(`br (`var z, entry, sse))

  let register_save_sse env label s =
    let+ save =
      Array.to_list sse_args |>
      List.mapi ~f:(fun i r -> i64 (i * 16 + rsave_sse_ofs), r) |>
      Context.List.map ~f:(fun (o, r) ->
          let* o, oi = Cv.Abi.binop (`add `i64) (`var s) o in
          let+ st = Cv.Abi.storev r (`var o) in
          [oi; st]) in
    let entry = `label (Func.entry env.fn, []) in
    Abi.Blk.create () ~label ~insns:(List.concat save) ~ctrl:(`jmp entry)

  let compute_register_save_area env =
    if needs_register_save env then
      let* rsslot = new_slot env 176 16 in
      let* sse = Context.Label.fresh in
      let* rsint = register_save_int env sse rsslot in
      let+ rssse = register_save_sse env sse rsslot in
      env.rsave <- Some {rsslot; rsint; rssse}
    else !!()

  (* Lower the parameters of the function and copy their contents
     to SSA variables or stack slots. *)
  let lower env =
    let* reg, reg2 = init_regs env in
    let* () =
      Func.args env.fn |>
      Context.Seq.iter ~f:(fun (x, t) -> match t with
          | #Type.basic as t -> basic_param ~reg env t x
          | `name s ->
            let* k = type_cls env s in
            let* y = new_slot env k.size k.align in
            Hashtbl.set env.refs ~key:x ~data:y;
            match k.cls with
            | Kreg _ when k.size = 0 -> !!()
            | Kreg (r, _) when k.size = 8 -> onereg_param ~reg env x y r
            | Kreg (r1, r2) -> tworeg_param ~reg2 env y r1 r2
            | Kmem -> memory_param env y k.size) in
    compute_register_save_area env
end

module Refs = struct
  let make_ref env i b x y = match Hashtbl.find env.refs y with
    | Some z -> !!(Hashtbl.set env.canon_ref ~key:x ~data:z)
    | None -> typeof_var env y >>= function
      | `compound (s, _, _) | `opaque (s, _, _) ->
        let* k = type_cls env s in
        let*? s = Slot.create x ~size:k.size ~align:k.align in
        Hashtbl.set env.refs ~key:y ~data:x;
        Vec.push env.slots s;
        !!()
      | t ->
        Context.failf
          "Expected compound type for instruction %a \
           in block %a of function $%s, got %a"
          Insn.pp i Label.pp (Blk.label b)
          (Func.name env.fn) Type.pp t ()

  let ref_oper = function
    | #operand as o -> oper o
    | `addr a -> `int (a, `i64)

  let make_unref env x s a =
    if not @@ Hashtbl.mem env.refs x then
      let* k = type_cls env s in
      let* y = new_slot env k.size k.align in
      let* src, srci = match a with
        | `var x -> !!(x, [])
        | _ ->
          let+ x, i = Cv.Abi.unop (`copy `i64) (ref_oper a) in
          x, [i] in
      let+ blit = Cv.Abi.blit ~src:(`var src) ~dst:(`var y) `i64 k.size in
      Hashtbl.set env.unrefs ~key:x ~data:(srci @ blit);
      Hashtbl.set env.refs ~key:x ~data:y
    else !!()

  (* Turn struct refs into a minimal number of stack slots, such
     that the result of each `ref` and `unref` instruction is
     accounted for, as well as any `call` or `vaarg` instruction
     that may return a struct. *)
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
          | `vaarg (x, `name s, _)
          | `call (Some (x, `name s), _, _, _) ->
            let* k = type_cls env s in
            if k.size > 0 then
              let+ y = new_slot env k.size k.align in
              Hashtbl.set env.refs ~key:x ~data:y
            else !!()
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
    let+ r = Cv.Abi.insn @@ `uop (`reg reg, `copy t, oper x) in
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
  let onereg_ret env r key x =
    let* x = expect_ret_var env key x in
    let x = find_ref env x in
    let t = reg_type r in
    let reg = match t with
      | `i64 -> int_rets.(0)
      | `f64 -> sse_rets.(0) in
    let+ r = Cv.Abi.insn @@ `load (`reg reg, t, `var x) in
    Hashtbl.set env.rets ~key ~data:{reti = [r]; retr = [reg]}

  (* Struct is returned in two registers of varying classes. *)
  let tworeg_ret env r1 r2 key x =
    let* x = expect_ret_var env key x in
    let x = find_ref env x in
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let reg1, reg2 = match t1, t2 with
      | `i64, `i64 -> int_rets.(0), int_rets.(1)
      | `i64, `f64 -> int_rets.(0), sse_rets.(0)
      | `f64, `f64 -> sse_rets.(0), sse_rets.(1)
      | `f64, `i64 -> sse_rets.(0), int_rets.(0) in
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
      let* k = type_cls env n in
      match k.cls with
      | Kreg _ when k.size = 0 -> go @@ fun key _ ->
        (* Struct is empty, so we return nothing. *)
        !!(Hashtbl.set env.rets ~key ~data:empty_ret)
      | Kreg (r, _) when k.size = 8 -> go @@ onereg_ret env r
      | Kreg (r1, r2) -> go @@ tworeg_ret env r1 r2
      | Kmem -> go @@ memory_ret env k
end

module Calls = struct
  (* A compound argument to a call passed in a single register. *)
  let onereg_arg ~reg k r src =
    let t = reg_type r in
    let* l, li = Cv.Abi.load t (`var src) in
    let+ callai, callar, callam = match reg r with
      | Some r ->
        let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy t, `var l) in
        k.callai @>* [li; i],
        k.callar @> r,
        k.callam
      | None ->
        !!(k.callai @> li,
           k.callar,
           k.callam @> `var l) in
    {k with callai; callar; callam}

  (* A compound argument to a call passed in two registers. *)
  let tworeg_arg ~reg2 k r1 r2 src =
    let t1 = reg_type r1 and t2 = reg_type r2 in
    let regs = reg2 r1 r2 in
    let* o, oi = Cv.Abi.binop (`add `i64) (`var src) o8 in
    let* l1, li1 = Cv.Abi.load `i64 (`var src) in
    let* l2, li2 = Cv.Abi.load `i64 (`var o) in
    let+ callai, callar, callam = match regs with
      | Some (r1, r2) ->
        let* i1 = Cv.Abi.insn @@ `uop (`reg r1, `copy t1, `var l1) in
        let+ i2 = Cv.Abi.insn @@ `uop (`reg r2, `copy t2, `var l2) in
        k.callai @>* [li1; oi; li2; i1; i2],
        k.callar @>* [r1; r2],
        k.callam
      | None ->
        !!(k.callai @>* [li1; oi; li2],
           k.callar,
           k.callam @>* [`var l1; `var l2]) in
    {k with callai; callar; callam}

  (* A compound argument to a call passed in memory. *)
  let memory_arg k size src =
    let+ ldm = Cv.Abi.ldm `i64 src size in
    let callai, callam =
      List.fold ldm ~init:(k.callai, k.callam) ~f:(fun (ai, am) i ->
          let am = match Abi.Insn.op i with
            | `load (x, _, _) -> am @> (x :> Abi.operand)
            | _ -> am in
          ai @> i, am) in
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
    {k with callri = k.callri @> i; callrr = [r]}

  (* Fits in one register. *)
  let call_ret_onereg env x r k =
    let x = find_ref env x in
    let t = reg_type r in
    let reg = match t with
      | `i64 -> int_rets.(0)
      | `f64 -> sse_rets.(0) in
    let+ st = Cv.Abi.store t (`reg reg) (`var x) in
    {k with callri = k.callri @> st; callrr = [reg]}

  (* Fits in two registers. *)
  let call_ret_tworeg env x r1 r2 k =
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
    let callri = k.callri @>* [oi; st1; st2] in
    {k with callri; callrr = [reg1; reg2]}

  (* Passed as a reference to memory. We need to allocate
     a new stack slot for this one. *)
  let call_ret_memory env x lk k =
    let r = int_args.(0) in
    let* y = new_slot env lk.size lk.align in
    let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy `i64, `var y) in
    let callai = k.callai @> i in
    let callar = r <@ k.callar in
    Hashtbl.set env.refs ~key:x ~data:y;
    {k with callai; callar; callrr = [int_rets.(0)]}

  (* Handle the compound type return value of a call.  *)
  let lower_call_ret env kret k = match kret with
    | `none -> !!k
    | `basic (x, t) -> call_ret_basic x t k
    | `compound (x, lk) -> match lk.cls with
      | Kreg _ when lk.size = 0 -> !!k
      | Kreg (r, _) when lk.size = 8 -> call_ret_onereg env x r k
      | Kreg (r1, r2) -> call_ret_tworeg env x r1 r2 k
      | Kmem -> call_ret_memory env x lk k

  let expect_arg_var env l : operand -> Var.t Context.t = function
    | `var x -> !!x
    | x ->
      Context.failf
        "Expected var for `call` operand in block %a \
         of function $%s, got %a" Label.pp l
        (Func.name env.fn) pp_operand x ()

  (* Figure out how we should pass the argument `a` at the call site. *)
  let classify_call_arg ~reg ~reg2 env key k a =
    typeof_operand env a >>= function
    | #Type.imm as m ->
      (* Use an integer register. *)
      begin match reg Rint with
        | None -> !!{k with callam = k.callam @> oper a}
        | Some r ->
          let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy m, oper a) in
          let callai = k.callai @> i in
          let callar = k.callar @> r in
          {k with callai; callar}
      end
    | #Type.fp as f ->
      (* Use an SSE register. *)
      begin match reg Rsse with
        | None -> !!{k with callam = k.callam @> oper a}
        | Some r ->
          let+ i = Cv.Abi.insn @@ `uop (`reg r, `copy f, oper a) in
          let callai = k.callai @> i in
          let callar = k.callar @> r in
          {k with callai; callar}
      end
    | `flag -> assert false
    | `compound (s, _, _) | `opaque (s, _, _) ->
      (* Figure out what class this type is. *)
      let* lk = type_cls env s in
      let* x = expect_arg_var env key a in
      let src = find_ref env x in
      match lk.cls with
      | Kreg _ when lk.size = 0 -> !!k
      | Kreg (r, _) when lk.size = 8 -> onereg_arg ~reg k r src
      | Kreg (r1, r2) -> tworeg_arg ~reg2 k r1 r2 src
      | Kmem -> memory_arg k lk.size (`var src)

  (* See `Param.alloc_onereg`. *)
  let alloc_onereg qs qi = function
    | Rint -> Stack.pop qi
    | Rsse -> Stack.pop qs
    | Rnone -> assert false

  (* See `Param.alloc_tworeg`. *)
  let alloc_tworeg qi qs r1 r2 = match r1, r2 with
    | Rint, Rint ->
      if Stack.length qi >= 2 then
        let r1 = Stack.pop_exn qi in
        let r2 = Stack.pop_exn qi in
        Some (r1, r2)
      else None
    | Rsse, Rsse ->
      if Stack.length qs >= 2 then
        let r1 = Stack.pop_exn qs in
        let r2 = Stack.pop_exn qs in
        Some (r1, r2)
      else None
    | Rint, Rsse ->
      if Stack.length qi >= 1
      && Stack.length qs >= 1 then
        let r1 = Stack.pop_exn qi in
        let r2 = Stack.pop_exn qs in
        Some (r1, r2)
      else None
    | Rsse, Rint ->
      if Stack.length qs >= 1
      && Stack.length qi >= 1 then
        let r1 = Stack.pop_exn qs in
        let r2 = Stack.pop_exn qi in
        Some (r1, r2)
      else None
    | Rnone, _ | _, Rnone -> assert false

  (* Lower the `call` instructions. *)
  let lower env = iter_blks env ~f:(fun b ->
      Blk.insns b |> Context.Seq.iter ~f:(fun i ->
          match Insn.op i with
          | `call (ret, _, args, vargs) ->
            let key = Insn.label i in
            let qi = int_arg_queue () in
            let qs = sse_arg_queue () in
            let reg = alloc_onereg qi qs in
            let reg2 = alloc_tworeg qi qs in
            (* See if we're returning a compound type. *)
            let* kret = match ret with
              | Some (x, `name n) ->
                (* Check for implicit first parameter. *)
                let* lk = type_cls env n in
                begin match lk.cls with
                  | Kmem -> ignore (Stack.pop_exn qi)
                  | _ -> ()
                end;
                !!(`compound (x, lk))
              | Some (x, t) -> !!(`basic (x, t))
              | None -> !!`none in
            (* Process each argument. *)
            let acls = classify_call_arg ~reg ~reg2 env key in
            let* k = Context.List.fold args ~init:empty_call ~f:acls in
            let* k = Context.List.fold vargs ~init:k ~f:acls in
            (* If this is a variadic call, then RAX must hold the number
               of SSE registers that were used to pass parameters. *)
            let* k = match vargs with
              | [] -> !!k
              | _ ->
                let n = num_sse_args - Stack.length qs in
                let+ i = Cv.Abi.insn @@ `uop (`reg "RAX", `copy `i8, i8 n) in
                {k with callai = k.callai @> i} in
            (* Process the return value. *)
            let+ k = lower_call_ret env kret k in
            Hashtbl.set env.calls ~key ~data:k
          | _ -> !!()))
end

module Vastart = struct
  let ap_oper : global -> Abi.operand = function
    | `addr a -> `int (a, `i64)
    | `sym _ as s -> s
    | `var _ as v -> v

  (* Initialize the `va_list` structure, which is defined as follows:

     typedef struct {
       unsigned int gp_offset;
       unsigned_int fp_offset;
       void *overflow_arg_area;
       void *reg_save_area;
     } va_list[1];

     where

     `gp_offset` and `fp_offset` are the offsets into the register
     save area for the next available integer and SSE registers,
     respectively

     `overflow_arg_area` is a pointer to the next available parameter
     that was passed on the stack

     `reg_save_area` is the start of the register save area
  *)
  let lower env = match env.rsave with
    | None -> !!()
    | Some rs -> iter_blks env ~f:(fun b ->
        Blk.insns b |> Context.Seq.iter ~f:(fun i ->
            match Insn.op i with
            | `vastart ap ->
              let ap = ap_oper ap in
              (* Compute `gp_offset` and `fp_offset`. *)
              let gp, fp =
                Vec.fold env.params ~init:(0, 48) ~f:(fun (gp, fp) p ->
                    match p.pvar, p.pty with
                    | `reg _, #Type.imm -> gp + 8, fp
                    | `reg _, #Type.fp -> gp, fp + 16
                    | `var _, _ -> gp, fp) in
              (* Initialize `gp_offset`. *)
              let* gpi = Cv.Abi.store `i32 (i32 gp) ap in
              (* Initialize `fp_offset`. *)
              let* o, oi1 = Cv.Abi.binop (`add `i64) ap o4 in
              let* fpi = Cv.Abi.store `i32 (i32 fp) (`var o) in
              (* Initialize `overflow_arg_area`.
                 XXX: what if we want to omit frame pointers? *)
              let* r, ri = Cv.Abi.binop (`add `i64) (`reg "RBP") o16 in
              let* o, oi2 = Cv.Abi.binop (`add `i64) ap o8 in
              let* ofi = Cv.Abi.store `i64 (`var r) (`var o) in
              (* Initialize `reg_save_area`. *)
              let* o, oi3 = Cv.Abi.binop (`add `i64) ap o16 in
              let+ rs = Cv.Abi.store `i64 (`var rs.rsslot) (`var o) in
              (* Store the result. *)
              let key = Insn.label i in
              let data = [gpi; oi1; fpi; ri; oi2; ofi; oi3; rs] in
              Hashtbl.set env.vastart ~key ~data
            | _ -> !!()))
end

module Vaarg = struct
  (* Rough sketch of the logic behind `vaarg` for a given type `t`:

     @bcmp:
       %a = add.l %ap, ofs     ; Load gp or fp offset.
       %o = ld.w %a            ;
       %c = le.w %o, limit-inc ; Check to see if we've exhausted the
       br %c, @breg, @bstk     ; register save area.
     @breg:
       %a = add.l %ap, 16      ; Load `reg_save_area`.
       %l = ld.l %a            ;
       %r = add.l %l, %o       ; Pointer to the next register.
       %n = add.w %o, inc      ; Increment the offset.
       %a = add.l %ap, ofs     ; Update the offset in %ap.
       st.w %n, %a             ;
       jmp @bjoin(%r)
     @bstk:
       %a = add.l %ap, 8       ; Load `overflow_arg_area`; this is
       %l = ld.l %a            ; the next arg on the stack.
       %n = add.l %l, 8        ; Increment by 8.
       st.l %n, %a             ; Update the pointer.
       jmp @bjoin(%l)
     @bjoin(%p):
       %x = ld.t %p            ; Return the fetched type.
       jmp @cont               ; Resume execution.
  *)
  let onereg env x t ap cont =
    let* lcmp = Context.Label.fresh in
    let* lreg = Context.Label.fresh in
    let* lstk = Context.Label.fresh in
    let* ljoin = Context.Label.fresh in
    let ofs, limit, inc = match t with
      | #Type.imm -> 0, 48, 8
      | #Type.fp -> 4, 176, 16 in
    (* Check the offset in the va_list to see if we should
       access the register save area or the overflow save
       area. *)
    let* o, oi =
      if ofs = 0 then
        let+ o, oi = Cv.Abi.load `i32 ap in
        o, [oi]
      else
        let* a, ai = Cv.Abi.binop (`add `i64) ap (i64 ofs) in
        let+ o, oi = Cv.Abi.load `i32 (`var a) in
        o, [ai; oi] in
    let* c, ci = Cv.Abi.binop (`le `i32) (`var o) (i32 (limit - inc)) in
    let locreg = `label (lreg, []) in
    let locstk = `label (lstk, []) in
    let bcmp =
      Abi.Blk.create ()
        ~label:lcmp
        ~insns:(oi @ [ci])
        ~ctrl:(`br (`var c, locreg, locstk)) in
    (* Access the register save area and increment the reg
       offset. *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o16 in
    let* l, li = Cv.Abi.load `i64 (`var a) in
    let* r, ri = Cv.Abi.binop (`add `i64) (`var l) (`var o) in
    let* n, ni = Cv.Abi.binop (`add `i32) (`var o) (i32 inc) in
    let* st =
      if ofs = 0 then
        let+ st = Cv.Abi.store `i32 (`var n) ap in
        [st]
      else
        let* a, ai = Cv.Abi.binop (`add `i64) ap (i64 ofs) in
        let+ st = Cv.Abi.store `i32 (`var n) (`var a) in
        [ai; st] in
    let breg =
      Abi.Blk.create ()
        ~label:lreg
        ~insns:([ai; li; ri; ni] @ st)
        ~ctrl:(`jmp (`label (ljoin, [`var r]))) in
    (* Access the overflow arg area and increment it. *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
    let* l, li = Cv.Abi.load `i64 (`var a) in
    let* n, ni = Cv.Abi.binop (`add `i64) (`var l) o8 in
    let* st = Cv.Abi.store `i64 (`var n) (`var a) in
    let bstk =
      Abi.Blk.create ()
        ~label:lstk
        ~insns:[ai; li; ni; st]
        ~ctrl:(`jmp (`label (ljoin, [`var l]))) in
    (* Join the results. *)
    let* p = Context.Var.fresh in
    (* Check if this is a struct; if so we need to blit it
       to the appropriate stack slot. *)
    let* res = match Hashtbl.find env.refs x with
      | None ->
        let+ li = Cv.Abi.insn @@ `load (`var x, t, `var p) in
        [li]
      | Some y ->
        let* l, li = Cv.Abi.load t (`var p) in
        let+ st = Cv.Abi.store t (`var l) (`var y) in
        [li; st] in
    let bjoin =
      Abi.Blk.create ()
        ~label:ljoin
        ~args:[p]
        ~insns:res
        ~ctrl:(`jmp (`label (cont, []))) in
    !![bcmp; breg; bstk; bjoin]

  (* Similar to `onereg`, but checks two integer registers at
     the same time. *)
  let tworeg_int env x ap cont =
    let* lcmp = Context.Label.fresh in
    let* lreg = Context.Label.fresh in
    let* lstk = Context.Label.fresh in
    let* ljoin = Context.Label.fresh in
    (* Check if `gp_offset` can support at least two registers. *)
    let* o, oi = Cv.Abi.load `i32 ap in
    let* c, ci = Cv.Abi.binop (`le `i32) (`var o) (i32 (48 - 16)) in
    let locreg = `label (lreg, []) in
    let locstk = `label (lstk, []) in
    let bcmp =
      Abi.Blk.create ()
        ~label:lcmp
        ~insns:[oi; ci]
        ~ctrl:(`br (`var c, locreg, locstk)) in
    (* Access the register save area and increment. *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o16 in
    let* l, li = Cv.Abi.load `i64 (`var a) in
    let* r, ri = Cv.Abi.binop (`add `i64) (`var l) (`var o) in
    let* n, ni = Cv.Abi.binop (`add `i32) (`var o) (i32 16) in
    let* st = Cv.Abi.store `i32 (`var n) ap in
    let breg =
      Abi.Blk.create ()
        ~label:lreg
        ~insns:[ai; li; ri; ni; st]
        ~ctrl:(`jmp (`label (ljoin, [`var r]))) in
    (* Access the overflow arg area and increment *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
    let* l, li = Cv.Abi.load `i64 (`var a) in
    let* n, ni = Cv.Abi.binop (`add `i64) (`var l) o16 in
    let* st = Cv.Abi.store `i64 (`var n) (`var a) in
    let bstk =
      Abi.Blk.create ()
        ~label:lstk
        ~insns:[ai; li; ni; st]
        ~ctrl:(`jmp (`label (ljoin, [`var l]))) in
    (* Join the results. *)
    let* p = Context.Var.fresh in
    let y = find_ref env x in
    let+ blit = Cv.Abi.blit `i64 16 ~src:(`var p) ~dst:(`var y) in
    let bjoin =
      Abi.Blk.create ()
        ~label:ljoin
        ~args:[p]
        ~insns:blit
        ~ctrl:(`jmp (`label (cont, []))) in
    [bcmp; breg; bstk; bjoin]

  (* Similar to `onereg`, but checks two SSE registers at
     the same time. *)
  let tworeg_sse env x ap cont =
    let* lcmp = Context.Label.fresh in
    let* lreg = Context.Label.fresh in
    let* lstk = Context.Label.fresh in
    let* ljoin = Context.Label.fresh in
    (* Check if `fp_offset` can support at least two registers. *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o4 in
    let* o, oi = Cv.Abi.load `i32 (`var a) in
    let* c, ci = Cv.Abi.binop (`le `i32) (`var o) (i32 (176 - 32)) in
    let locreg = `label (lreg, []) in
    let locstk = `label (lstk, []) in
    let bcmp =
      Abi.Blk.create ()
        ~label:lcmp
        ~insns:[oi; ai; ci]
        ~ctrl:(`br (`var c, locreg, locstk)) in
    (* Access the register save area and increment. *)
    let* a, ai1 = Cv.Abi.binop (`add `i64) ap o16 in
    let* l, li = Cv.Abi.load `i64 (`var a) in
    let* r, ri = Cv.Abi.binop (`add `i64) (`var l) (`var o) in
    let* n, ni = Cv.Abi.binop (`add `i32) (`var o) (i32 32) in
    let* a, ai2 = Cv.Abi.binop (`add `i64) ap o4 in
    let* st = Cv.Abi.store `i32 (`var n) (`var a) in
    let breg =
      Abi.Blk.create ()
        ~label:lreg
        ~insns:[ai1; li; ri; ni; ai2; st]
        ~ctrl:(`jmp (`label (ljoin, [`var r]))) in
    (* Access the overflow arg area and increment *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
    let* l, li = Cv.Abi.load `i64 (`var a) in
    let* n, ni = Cv.Abi.binop (`add `i64) (`var l) o16 in
    let* st = Cv.Abi.store `i64 (`var n) (`var a) in
    let bstk =
      Abi.Blk.create ()
        ~label:lstk
        ~insns:[ai; li; ni; st]
        ~ctrl:(`jmp (`label (ljoin, [`var l]))) in
    (* Join the results. *)
    let* p = Context.Var.fresh in
    let y = find_ref env x in
    let+ blit = Cv.Abi.blit `i64 16 ~src:(`var p) ~dst:(`var y) in
    let bjoin =
      Abi.Blk.create ()
        ~label:ljoin
        ~args:[p]
        ~insns:blit
        ~ctrl:(`jmp (`label (cont, []))) in
    [bcmp; breg; bstk; bjoin]

  let make_cmp label t ap yes no =
    let* o, a, oi, limit, inc = match t with
      | `i64 ->
        let+ o, oi = Cv.Abi.load `i32 ap in
        o, ap, [oi], 48, 8
      | `f64 ->
        let* a, ai = Cv.Abi.binop (`add `i64) ap o4 in
        let+ o, oi = Cv.Abi.load `i32 (`var a) in
        o, `var a, [ai; oi], 176, 16 in
    let+ c, ci = Cv.Abi.binop (`le `i32) (`var o) (i32 (limit - inc)) in
    let b = Abi.Blk.create () ~label
        ~insns:(oi @ [ci])
        ~ctrl:(`br (`var c, `label (yes, []), `label (no, []))) in
    b, o, a, inc

  (* Fetches two register classes at once, assuming that they are
     different. *)
  let tworeg_mixed env x t1 t2 ap cont =
    let* lcmp1 = Context.Label.fresh in
    let* lcmp2 = Context.Label.fresh in
    let* lreg = Context.Label.fresh in
    let* lstk = Context.Label.fresh in
    let* ljoin = Context.Label.fresh in
    (* Check if both registers can be fetched from the register
       save area. *)
    let* bcmp1, o1, a1, inc1 = make_cmp lcmp1 t1 ap lcmp2 lstk in
    let* bcmp2, o2, a2, inc2 = make_cmp lcmp2 t2 ap lreg lstk in
    (* Access the register save area and increment. *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o16 in
    let* l, li = Cv.Abi.load `i64 (`var a) in
    let* r1, ri1 = Cv.Abi.binop (`add `i64) (`var l) (`var o1) in
    let* r2, ri2 = Cv.Abi.binop (`add `i64) (`var l) (`var o2) in
    let* n1, ni1 = Cv.Abi.binop (`add `i32) (`var o1) (i64 inc1) in
    let* n2, ni2 = Cv.Abi.binop (`add `i32) (`var o2) (i64 inc2) in
    let* st1 = Cv.Abi.store `i32 (`var n1) a1 in
    let* st2 = Cv.Abi.store `i32 (`var n2) a2 in
    let breg =
      Abi.Blk.create ()
        ~label:lreg
        ~insns:[ai; li; ri1; ri2; ni1; ni2; st1; st2]
        ~ctrl:(`jmp (`label (ljoin, [`var r1; `var r2]))) in
    (* Access the overflow arg area and increment *)
    let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
    let* l1, li1 = Cv.Abi.load `i64 (`var a) in
    let* l2, li2 = Cv.Abi.binop (`add `i64) (`var l1) o8 in
    let* n, ni = Cv.Abi.binop (`add `i64) (`var l1) o16 in
    let* st = Cv.Abi.store `i64 (`var n) (`var a) in
    let bstk =
      Abi.Blk.create ()
        ~label:lstk
        ~insns:[ai; li1; li2; ni; st]
        ~ctrl:(`jmp (`label (ljoin, [`var l1; `var l2]))) in
    (* Join the results. *)
    let* p1 = Context.Var.fresh in
    let* p2 = Context.Var.fresh in
    let y = find_ref env x in
    let t1b = (t1 :> Type.basic) in
    let t2b = (t2 :> Type.basic) in
    let* l, li1 = Cv.Abi.load t1b (`var p1) in
    let* st1 = Cv.Abi.store t1b (`var l) (`var y) in
    let* l, li2 = Cv.Abi.load t2b (`var p2) in
    let* a, ai = Cv.Abi.binop (`add `i64) (`var y) o8 in
    let+ st2 = Cv.Abi.store t2b (`var l) (`var a) in
    let bjoin =
      Abi.Blk.create ()
        ~label:ljoin
        ~args:[p1; p2]
        ~insns:[li1; st1; li2; ai; st2]
        ~ctrl:(`jmp (`label (cont, []))) in
    [bcmp1; bcmp2; breg; bstk; bjoin]

  let fetch env x t ap cont = match (t : Type.arg) with
    | #Type.imm as m -> onereg env x m ap cont
    | #Type.fp as f -> onereg env x f ap cont
    | `name s ->
      let* k = type_cls env s in
      match k.cls with
      | Kreg _ when k.size = 0 -> !![]
      | Kreg (r, _) when k.size = 8 ->
        assert (Hashtbl.mem env.refs x);
        begin match reg_type r with
          | `i64 -> onereg env x `i64 ap cont
          | `f64 -> onereg env x `f64 ap cont
        end
      | Kreg (r1, r2) ->
        begin match reg_type r1, reg_type r2 with
          | `i64, `i64 -> tworeg_int env x ap cont
          | `f64, `f64 -> tworeg_sse env x ap cont
          | t1, t2 -> tworeg_mixed env x t1 t2 ap cont
        end
      | Kmem ->
        (* The struct is passed in nemory, so we simply blit from
           the `overflow_arg_area` to the corresponding stack slot. *)
        let y = find_ref env x in
        let* label = Context.Label.fresh in
        let* a, ai = Cv.Abi.binop (`add `i64) ap o8 in
        let* l, li = Cv.Abi.load `i64 (`var a) in
        let* n, ni = Cv.Abi.binop (`add `i64) (`var l) (i64 k.size) in
        let* st = Cv.Abi.store `i64 (`var n) (`var a) in
        let+ blit = Cv.Abi.blit `i64 k.size
            ~src:(`var l) ~dst:(`var y) in
        List.return @@ Abi.Blk.create () ~label
          ~insns:([ai; li; ni; st] @ blit)
          ~ctrl:(`jmp (`label (cont, [])))

  let lower env = iter_blks env ~f:(fun b ->
      Blk.insns b |> Context.Seq.iter ~f:(fun i ->
          match Insn.op i with
          | `vaarg (x, t, ap) ->
            let ap = Vastart.ap_oper ap in
            let* vacont = Context.Label.fresh in
            let+ vablks = fetch env x t ap vacont in
            if not @@ List.is_empty vablks then
              Hashtbl.set env.vaarg
                ~key:(Insn.label i)
                ~data:{vablks; vacont}
          | _ -> !!()))
end

(* Actually produce a Virtual ABI function from the work done in
   the above passes. *)
module Translate = struct
  let transl_var env x =
    match Hashtbl.find env.canon_ref x with
    | Some y -> y
    | None -> match Hashtbl.find env.refs x with
      | Some y -> y
      | None -> x

  let transl_operand env : operand -> Abi.operand = function
    | `var x -> `var (transl_var env x)
    | o -> oper o

  let transl_local env : local -> Abi.local = function
    | `label (l, args) ->
      `label (l, List.map args ~f:(transl_operand env))

  let transl_global env : global -> Abi.global = function
    | `var x -> `var (`var (transl_var env x))
    | (`addr _ | `sym _) as g -> g

  let transl_dst env : dst -> Abi.dst = function
    | #local as l -> (transl_local env l :> Abi.dst)
    | #global as g -> (transl_global env g :> Abi.dst)

  let transl_basic env (b : Insn.basic) : Abi.Insn.basic =
    let op = transl_operand env in
    match b with
    | `bop (x, b, l, r) -> `bop (`var x, b, op l, op r)
    | `uop (x, u, a) -> `uop (`var x, u, op a)
    | `sel (x, t, c, l, r) -> `sel (`var x, t, `var c, op l, op r)

  let transl_mem env (m : Insn.mem) : Abi.Insn.mem =
    let op = transl_operand env in
    match m with
    | `load (x, t, a) -> `load (`var x, t, op a)
    | `store (t, v, a) -> `store (t, op v, op a)

  let transl_call env ivec l f =
    let k = Hashtbl.find_exn env.calls l in
    (* Instructions before the call. *)
    Ftree.iter k.callai ~f:(Vec.push ivec);
    (* Register and memory arguments. *)
    let rargs =
      Ftree.to_list k.callar |>
      List.map ~f:(fun r -> `reg r) in
    let margs = Ftree.to_list k.callam in
    (* The call itself. *)
    let c = `call (k.callrr, transl_global env f, rargs @ margs) in
    Vec.push ivec @@ Abi.Insn.create ~label:l c;
    (* Instructions after the call. *)
    Ftree.iter k.callri ~f:(Vec.push ivec)

  let transl_compound env ivec (c : Insn.compound) = match c with
    | `ref _ -> ()
    | `unref (x, _, _) ->
      Hashtbl.find env.unrefs x |>
      Option.iter ~f:(List.iter ~f:(Vec.push ivec))

  let transl_insn env ivec i =
    let l = Insn.label i in
    let ins = Abi.Insn.create ~label:l in
    match Insn.op i with
    | #Insn.basic as b ->
      Vec.push ivec @@
      ins (transl_basic env b :> Abi.Insn.op)
    | #Insn.mem as m ->
      Vec.push ivec @@
      ins (transl_mem env m :> Abi.Insn.op)
    | #Insn.compound as c ->
      transl_compound env ivec c
    | `vastart _ ->
      Hashtbl.find_exn env.vastart l |>
      List.iter ~f:(Vec.push ivec)
    | `call (_, f, _, _) ->
      transl_call env ivec l f
    | `vaarg _ ->
      (* Should be handled in `transl_blk`. *)
      assert false

  let transl_swindex env = function
    | `var x -> `var (`var (transl_var env x))
    | `sym s -> `sym s

  let transl_tbl env tbl t =
    Ctrl.Table.enum tbl |>
    Seq.map ~f:(fun (v, l) -> v, transl_local env l) |>
    Seq.to_list |> fun tbl ->
    Abi.Ctrl.Table.create_exn tbl t 

  let transl_sw env t i d tbl =
    `sw (t, transl_swindex env i, transl_local env d, transl_tbl env tbl t)

  let transl_ret env l =
    let r = Hashtbl.find_exn env.rets l in
    r.reti, `ret r.retr

  let transl_ctrl env l (c : ctrl) : Abi.insn list * Abi.ctrl =
    let dst = transl_dst env in
    match c with
    | `hlt -> [], `hlt
    | `jmp d -> [], `jmp (dst d)
    | `br (c, y, n) -> [], `br (`var (transl_var env c), dst y, dst n)
    | `sw (t, i, d, tbl) -> [], transl_sw env t i d tbl
    | `ret None -> [], `ret []
    | `ret Some _ -> transl_ret env l

  (* We're done translating this block, either because we translated
     all the remaining instructions or we had to split it in the
     `vaarg` case. *)
  let commit_blk ivec args (cins, ctrl) label =
    List.iter cins ~f:(Vec.push ivec);
    let insns = Vec.to_list ivec in
    Vec.clear ivec;
    Abi.Blk.create () ~args ~insns ~ctrl ~label

  (* Translate a single block, which may be split into multiple blocks. *)
  let rec transl_blk env ivec args ctrl label acc = function
    | i :: rest ->
      begin match Insn.op i with
        | `vaarg _ ->
          begin match Hashtbl.find env.vaarg @@ Insn.label i with
            | None -> transl_blk env ivec args ctrl label acc rest
            | Some v ->
              (* Jump to the start of the `vaarg` logic. *)
              let start = Abi.Blk.label @@ List.hd_exn v.vablks in
              let ctrl' = [], `jmp (`label (start, [])) in
              let b = commit_blk ivec args ctrl' label in
              (* Resume with the provided continuation. *)
              let init = Ftree.snoc acc b in
              let acc = List.fold v.vablks ~init ~f:Ftree.snoc in
              transl_blk env ivec [] ctrl v.vacont acc rest
          end
        | _ ->
          (* No splitting needed. *)
          transl_insn env ivec i;
          transl_blk env ivec args ctrl label acc rest
      end
    | [] ->
      commit_blk ivec args ctrl label |>
      Ftree.snoc acc |> Ftree.to_list

  let transl_blks env =
    let ivec = Vec.create () in
    let entry = Func.entry env.fn in
    Func.blks env.fn |> Seq.to_list |> List.bind ~f:(fun b ->
        let l = Blk.label b in
        (* Entry block copies the parameters. *)
        if Label.(l = entry) then
          Vec.iter env.params ~f:(fun p ->
              List.iter p.pins ~f:(Vec.push ivec));
        let args = Blk.args b |> Seq.to_list in
        let ctrl = transl_ctrl env l @@ Blk.ctrl b in
        transl_blk env ivec args ctrl l Ftree.empty @@
        Seq.to_list @@ Blk.insns b)

  let make_dict env =
    let lnk = Func.linkage env.fn in
    let dict = Dict.singleton Func.Tag.linkage lnk in
    let dict = if Func.variadic env.fn
      then Dict.set dict Func.Tag.variadic ()
      else dict in
    dict

  let go env =
    let slots = Func.slots env.fn |> Seq.to_list in
    let slots = slots @ Vec.to_list env.slots in
    let args =
      Vec.to_sequence_mutable env.params |>
      Seq.map ~f:(fun p -> p.pvar, p.pty) |>
      Seq.to_list in
    let blks = transl_blks env in
    let blks = match env.rsave with
      | Some r -> r.rsint :: r.rssse :: blks
      | None -> blks in
    Abi.Func.create () ~slots ~args ~blks
      ~name:(Func.name env.fn)
      ~dict:(make_dict env)
end

let run tenv fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let env = init_env tenv fn in
    let* () = Params.lower env in
    let* () = Refs.canonicalize env in
    let* () = Rets.lower env in
    let* () = Calls.lower env in
    let* () = Vastart.lower env in
    let* () = Vaarg.lower env in
    let*? fn = Translate.go env in
    !!fn
  else
    Context.failf
      "In Lower_abi: expected SSA form for function $%s"
      (Func.name fn) ()

