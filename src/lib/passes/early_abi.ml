open Core
open Regular.Std
open Virtual

open Context.Syntax

(* New instructions for a block. *)
type new_insns = {
  prepend : insn list Label.Table.t; (* Prepend to label. *)
  append  : insn list Label.Table.t; (* Append to label. *)
}

let init_new_insns () = {
  prepend = Label.Table.create ();
  append  = Label.Table.create ();
}

let clear_new_insns is =
  Hashtbl.clear is.prepend;
  Hashtbl.clear is.append

let prepend is l i =
  Hashtbl.add_multi is.prepend ~key:l ~data:i

let append is l i =
  Hashtbl.add_multi is.append ~key:l ~data:i

let update_blk_insns is b =
  let b = Hashtbl.fold is.prepend ~init:b ~f:(fun ~key:l ~data:is b ->
      Blk.prepend_insns ~before:l b @@ List.rev is) in
  let b = Hashtbl.fold is.append ~init:b ~f:(fun ~key:l ~data:is b ->
      Blk.append_insns ~after:l b @@ List.rev is) in
  b

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

(* RDI, RSI, RDX, RCX, R8, R9 *)
let num_int_args = 6

(* XMM0, XMM1, ..., XMM7 *)
let num_sse_args = 8

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

(* Lower the return instructions. *)
let selret tenv fn = match Func.return fn with
  | None | Some #Type.basic -> !!fn
  | Some `name n ->
    let*? lt = Typecheck.Env.layout n tenv in
    let k = classify_layout lt in
    let dict = Func.dict fn in
    match k.cls with
    | Kreg _ when k.size = 0 ->
      let dict = Dict.remove dict Func.Tag.return in
      let fn =
        Func.with_dict fn dict |>
        Func.map_blks ~f:(Blk.map_ctrl ~f:(function
            | `ret _ -> `ret None
            | c -> c)) in
      !!fn
    | Kreg (r, _) when k.size = 8 ->
      let rty = reg_type r in
      let dict = Dict.set dict Func.Tag.return rty in
      let fn = Func.with_dict fn dict in
      let* blks =
        Func.blks fn |> Context.Seq.filter_map ~f:(fun b ->
            match Blk.ctrl b with
            | `ret Some `var x ->
              let* r, ri = Context.Virtual.ref (`var x) in
              let+ l, ld = Context.Virtual.load rty (`var r) in
              let b = Blk.append_insns b [ri; ld] in
              let b = Blk.with_ctrl b @@ `ret (Some (`var l)) in
              Some b
            | _ -> !!None) in
      let*? fn = Func.update_blks fn @@ Seq.to_list blks in
      !!fn
    | Kreg _ ->
      (* If we're returning two registers, then we
         need to delay this step until instruction
         selection occurs. *)
      !!fn
    | Kmem ->
      (* The struct is returned in memory, which requires an implicit
         first parameter that we will blit its memory contents to. *)
      let dict = Dict.set dict Func.Tag.return `i64 in
      let fn = Func.with_dict fn dict in
      let* dst = Context.Var.fresh in
      let fn = Func.prepend_arg fn dst `i64 in
      let* blks = Func.blks fn |> Context.Seq.filter_map ~f:(fun b ->
          match Blk.ctrl b with
          | `ret Some `var x ->
            let* src, srci = Context.Virtual.ref (`var x) in
            let+ blit = Context.Virtual.blit ~src ~dst `i64 k.size in
            let b = Blk.append_insns b (srci :: blit) in
            let b = Blk.with_ctrl b @@ `ret (Some (`var dst)) in
            Some b
          | _ -> !!None) in
      let*? fn = Func.update_blks fn @@ Seq.to_list blks in
      !!fn

module Calls = struct
  type env = {
    fn    : func;
    tenv  : Typecheck.env;
    nins  : new_insns;
    mems  : operand Vec.t;
    slots : (Var.t * int * int) Vec.t;
  }

  let init_env fn tenv = {
    fn;
    tenv;
    nins = init_new_insns ();
    mems = Vec.create ();
    slots = Vec.create ();
  }

  (* A struct is classified as being passed in a single register. *)
  let onereg_arg ~decreg env label src r =
    let* l, li = Context.Virtual.load `i64 (`var src) in
    prepend env.nins label li;
    match decreg r with
    | false -> Vec.push env.mems @@ `var l; !![]
    | true -> !![`var l]

  (* A struct is classified as being passed in two registers. *)
  let tworeg_arg ~decreg env label src r1 r2 =
    let ok1 = decreg r1 in
    let ok2 = decreg r2 in
    let o = `int (Bv.M64.int 8, `i64) in
    let* o, oi = Context.Virtual.binop (`add `i64) (`var src) o in
    let* l1, li1 = Context.Virtual.load `i64 (`var src) in
    let* l2, li2 = Context.Virtual.load `i64 (`var o) in
    prepend env.nins label oi;
    prepend env.nins label li1;
    prepend env.nins label li2;
    match ok1, ok2 with
    | true, true ->
      !![`var l1; `var l2]
    | true, false ->
      Vec.push env.mems @@ `var l2;
      !![`var l1]
    | false, true  ->
      Vec.push env.mems @@ `var l1;
      !![`var l2]
    | false, false ->
      Vec.push env.mems @@ `var l1;
      Vec.push env.mems @@ `var l2;
      !![]

  (* A struct is classified as being passed in memory. *)
  let mem_arg env label src size =
    let+ ldm = Context.Virtual.ldm `i64 src size in
    List.iter ldm ~f:(fun i ->
        prepend env.nins label i;
        match Insn.op i with
        | `load (x, _, _) ->
          Vec.push env.mems @@ `var x
        | _ -> ());
    []

  (* Figure out how to compute the return value. *)
  let callret env label args ret kret = match kret with
    | None -> !!(args, ret)
    | Some (x, n, k) -> match k.cls with
      | Kreg _  ->
        (* We need access to specific registers, so we will delay
           this step until instruction selection. *)
        !!(args, ret)
      | Kmem ->
        let* y = Context.Var.fresh in
        let* z = Context.Var.fresh in
        let+ l = Context.Label.fresh in
        let i = Insn.create ~label:l @@ `unref (x, n, `var z) in
        Vec.push env.slots (y, k.size, k.align);
        append env.nins label i;
        (`var y :: args), Some (z, `i64)

  (* Classify an argument to a call. *)
  let argclass ~decreg env label nint nsse a =
    typeof_operand env.tenv env.fn a >>= function
    | #Type.imm when !nint <= 0 -> Vec.push env.mems a; !![]
    | #Type.imm when !nsse <= 0 -> Vec.push env.mems a; !![]
    | #Type.imm -> decr nint; !![a]
    | #Type.fp -> decr nsse; !![a]
    | `flag -> assert false
    | `compound (name, _, _) | `opaque (name, _, _) ->
      let*? lt = Typecheck.Env.layout name env.tenv in
      let k = classify_layout lt in
      let* src, srci = Context.Virtual.ref a in
      prepend env.nins label srci;
      match k.cls with
      | Kreg (r, _) when k.size = 8 ->
        onereg_arg ~decreg env label src r
      | Kreg (r1, r2) ->
        tworeg_arg ~decreg env label src r1 r2
      | Kmem ->
        mem_arg env label src k.size

  (* Process a single call instruction. *)
  let callins env label ret args vargs =
    let* kret = match ret with
      | Some (x, `name n) ->
        let*? lt = Typecheck.Env.layout n env.tenv in
        !!(Some (x, n, classify_layout lt))
      | Some _ | None -> !!None in
    (* Keep track of how many GPR and SSE registers are
       available. *)
    let nint = ref @@ match kret with
      | Some (_, _, {cls = Kmem; _}) -> num_int_args - 1
      | _ -> num_int_args in
    let nsse = ref num_sse_args in
    (* Decrement the corresponding register count and see
       if we need to pass the argument in memory. *)
    let decreg = function
      | Rint | Rnone when !nint <= 0 -> false
      | Rint | Rnone -> decr nint; true
      | Rsse when !nsse <= 0 -> false
      | Rsse -> decr nsse; true in
    (* Organize the arguments as being either in registers
       or memory. *)
    let* args' = Context.List.map (args @ vargs)
        ~f:(argclass ~decreg env label nint nsse) in
    let args' = List.concat args' in
    (* If we're returning a struct, then insert the implicit
       first parameter and create a new stack slot for it, if
       it is returned in memory. *)
    let+ args', ret = callret env label args' ret kret in
    let mems = Vec.to_list env.mems in
    Vec.clear env.mems;
    args', ret, mems

  (* Lower the call instructions. *)
  let selcall tenv fn =
    let env = init_env fn tenv in
    let* blks = Func.blks fn |> Context.Seq.map ~f:(fun b ->
        let+ insns = Blk.insns b |> Context.Seq.map ~f:(fun i ->
            match Insn.op i with
            | `call (ret, f, args, vargs) ->
              let label = Insn.label i in
              let+ args', ret, mems = callins env label ret args vargs in
              (* We can't have tail calls that require stack space for
                 their parameters. *)
              let i =
                if List.is_empty mems then i
                else Insn.(with_tag i Tag.non_tail ()) in
              (* XXX: this is a big hack and leaks our abstraction too
                 much, but I'm not sure what else can be done. Maybe it's
                 OK as long as this is well-documented. *)
              Insn.with_op i @@ `call (ret, f, args', mems)
            | _ -> !!i) in
        let b = Blk.with_insns b @@ Seq.to_list insns in
        let b = update_blk_insns env.nins b in
        clear_new_insns env.nins;
        b) in
    let*? fn = Func.update_blks fn @@ Seq.to_list blks in
    (* Insert the new stack slots. *)
    Vec.to_sequence_mutable env.slots |>
    Context.Seq.fold ~init:fn ~f:(fun fn (x, size, align) ->
        let*? s = Func.Slot.create x ~size ~align in
        !!(Func.insert_slot fn s))
end

let run tenv fn =
  let* fn = selret tenv fn in
  let* fn = Calls.selcall tenv fn in
  !!fn
