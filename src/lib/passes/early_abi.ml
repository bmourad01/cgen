open Core
open Regular.Std
open Virtual

open Context.Syntax

(* RDI, RSI, RDX, RCX, R8, R9 *)
let num_int_args = 6

(* XMM0, XMM1, ..., XMM7 *)
let num_sse_args = 8

type reg =
  | Rnone
  | Rint
  | Rsse
[@@deriving equal]

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

(* Prioritize larger loads. *)
let blits = [
  `i64, 8;
  `i32, 4;
  `i16, 2;
  `i8,  1;
]

let blit_struct ?(store = true) src dst size =
  let fwd = size >= 0 in
  let rec aux ty is sz off n = if sz >= n then
      let off = off - (if fwd then n else 0) in
      let o = `int (Bv.M64.int off, `i64) in
      (* Copy from src. *)
      let* a1, ai1 = Context.Virtual.binop (`add `i64) (`var src) o in
      let* l, ld = Context.Virtual.load ty (`var a1) in
      (* Store to dst. *)
      let* sts = if store then
          let* a2, ai2 = Context.Virtual.binop (`add `i64) (`var dst) o in
          let+ st = Context.Virtual.store ty (`var l) (`var a2) in
          [st; ai2]
        else !![] in
      (* Accumulate insns in reverse order. *)
      let is = sts @ (ld :: ai1 :: is) in
      let off = off + (if fwd then 0 else n) in
      aux ty is (sz - n) off n
    else !!(is, sz, off) in
  let+ blit, _, _ =
    let sz = Int.abs size in
    let off = if fwd then sz else 0 in
    Context.List.fold blits ~init:([], sz, off)
      ~f:(fun ((is, sz, off) as acc) (ty, by) ->
          if sz <= 0 then !!acc
          else aux ty is sz off by) in
  List.rev blit

let selret tenv fn = match Func.return fn with
  | None | Some #Type.basic -> !!fn
  | Some `name n ->
    let*? lt = Typecheck.Env.layout n tenv in
    let k = classify_layout lt in
    let dict = Func.dict fn in
    match k.cls with
    | Kreg (Rnone, Rnone) when k.size = 0 ->
      let dict = Dict.remove dict Func.Tag.return in
      Func.with_dict fn dict |>
      Func.map_blks ~f:(Blk.map_ctrl ~f:(function
          | `ret _ -> `ret None
          | c -> c)) |> Context.return
    | Kreg (_, Rnone) when k.size = 8 ->
      let dict = Dict.set dict Func.Tag.return `i64 in
      let fn = Func.with_dict fn dict in
      let* blks =
        Func.blks fn |> Context.Seq.filter_map ~f:(fun b ->
            match Blk.ctrl b with
            | `ret Some `var x ->
              let* r, ri = Context.Virtual.unop `ref (`var x) in
              let+ l, ld = Context.Virtual.load `i64 (`var r) in
              let b = Blk.append_insns b [ri; ld] in
              let b = Blk.with_ctrl b @@ `ret (Some (`var l)) in
              Some b
            | _ -> !!None) in
      Context.lift_err @@
      Func.update_blks fn @@
      Seq.to_list blks
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
      let* blks =
        Func.blks fn |> Context.Seq.filter_map ~f:(fun b ->
            match Blk.ctrl b with
            | `ret Some `var x ->
              let* src, srci = Context.Virtual.unop `ref (`var x) in
              let+ blit = blit_struct src dst k.size in
              let b = Blk.append_insns b (srci :: blit) in
              let b = Blk.with_ctrl b @@ `ret (Some (`var dst)) in
              Some b
            | _ -> !!None) in
      Context.lift_err @@
      Func.update_blks fn @@
      Seq.to_list blks

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

let selcall tenv fn =
  let* blks = Func.blks fn |> Context.Seq.map ~f:(fun b ->
      let ninsns = Label.Table.create () in
      let newins l i = Hashtbl.add_multi ninsns ~key:l ~data:i in
      let+ insns = Blk.insns b |> Context.Seq.map ~f:(fun i ->
          match Insn.op i with
          | `call (ret, f, args, vargs) ->
            let label = Insn.label i in
            let nint = ref @@ match ret with
              | Some (_, `name _) -> num_int_args - 1
              | _ -> num_int_args in
            let nsse = ref num_sse_args in
            let decreg = function
              | Rint | Rnone when !nint <= 0 -> false
              | Rint | Rnone -> decr nint; true
              | Rsse when !nsse <= 0 -> false
              | Rsse -> decr nsse; true in
            let mems = Vec.create () in
            let+ args' = Context.List.map (args @ vargs) ~f:(fun a ->
                typeof_operand tenv fn a >>= function
                | #Type.imm when !nint <= 0 -> Vec.push mems a; !![]
                | #Type.imm when !nsse <= 0 -> Vec.push mems a; !![]
                | #Type.imm -> decr nint; !![a]
                | #Type.fp -> decr nsse; !![a]
                | `flag -> assert false
                | `compound (name, _, _)
                | `opaque (name, _, _) ->
                  let*? lt = Typecheck.Env.layout name tenv in
                  let k = classify_layout lt in
                  let* src, srci = Context.Virtual.unop `ref a in
                  newins label srci;
                  match k.cls with
                  | Kreg (r1, r2) ->
                    let ok1 = decreg r1 in
                    let ok2 = decreg r2 in
                    let o = `int (Bv.M64.int 8, `i64) in
                    let* o, oi = Context.Virtual.binop (`add `i64) (`var src) o in
                    let* l1, li1 = Context.Virtual.load `i64 (`var src) in
                    let* l2, li2 = Context.Virtual.load `i64 (`var o) in
                    newins label oi;
                    newins label li1;
                    newins label li2;
                    begin match ok1, ok2 with
                      | true, true ->
                        !![`var l1; `var l2]
                      | true, false ->
                        Vec.push mems @@ `var l2;
                        !![`var l1]
                      | false, true ->
                        Vec.push mems @@ `var l1;
                        !![`var l2]
                      | false, false ->
                        Vec.push mems @@ `var l1;
                        Vec.push mems @@ `var l2;
                        !![]
                    end
                  | Kmem ->
                    let+ blit = blit_struct ~store:false src src k.size in
                    List.iter blit ~f:(fun i ->
                        newins label i;
                        match Insn.op i with
                        | `load (x, _, _) -> Vec.push mems @@ `var x
                        | _ -> ());
                    []) in
            (* XXX: this is a big hack and leaks our abstraction too much,
               but I'm not sure what else can be done. Maybe it's OK as long
               as this is well-documented.  *)
            Insn.with_op i @@ `call (ret, f, List.concat args', Vec.to_list mems)
          | _ -> !!i) in
      let b =
        Blk.with_insns b @@
        Seq.to_list insns in
      Hashtbl.fold ninsns ~init:b ~f:(fun ~key:l ~data:is b ->
          Blk.prepend_insns ~before:(Some l) b @@ List.rev is)) in
  Context.lift_err @@
  Func.update_blks fn @@
  Seq.to_list blks

let run tenv m =
  !!m
