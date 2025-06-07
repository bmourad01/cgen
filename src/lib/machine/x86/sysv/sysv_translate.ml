open Core
open Regular.Std
open Virtual
open Sysv_common

module Make(Context : Context_intf.S_virtual) = struct
  open Context.Syntax
  module Cv = Context.Virtual

  (* A block translation context. *)
  type transl = {
    ivec         : Abi.insn Vec.t; (* Pending instructions to be committed. *)
    bvec         : Abi.blk Vec.t;  (* Pending blocks to be committed. *)
    mutable args : Var.t list;     (* Arguments of the current block. *)
    mutable cins : Abi.insn list;  (* Instructions immediately before the `ctrl`. *)
    mutable ctrl : Abi.ctrl;       (* Current control flow instruction. *)
  }

  let create_transl () = {
    ivec = Vec.create ();
    bvec = Vec.create ();
    args = [];
    cins = [];
    ctrl = `hlt; (* dummy *)
  }

  let transl_var env x = match Hashtbl.find env.refs x with
    | Some y -> y
    | None -> x

  let transl_operand env : operand -> operand = function
    | `var x -> `var (transl_var env x)
    | o -> o

  let transl_local env : local -> local = function
    | `label (l, args) ->
      `label (l, List.map args ~f:(transl_operand env))

  let transl_global env : global -> global = function
    | `var x -> `var (transl_var env x)
    | (`addr _ | `sym _) as g -> g

  let transl_dst env : dst -> dst = function
    | #local as l -> (transl_local env l :> dst)
    | #global as g -> (transl_global env g :> dst)

  let transl_basic env (b : Insn.basic) : Abi.Insn.basic =
    let op = transl_operand env in
    match b with
    | `bop (x, b, l, r) -> `bop (x, b, op l, op r)
    | `uop (_, `uitof _, _) -> assert false
    | `uop (x, u, a) -> `uop (x, u, op a)
    | `sel (x, t, c, l, r) -> `sel (x, t, c, op l, op r)

  let transl_mem env ivec l (m : Insn.mem) =
    let op = transl_operand env in
    let ins = Abi.Insn.create ~label:l in
    match m with
    | `load (x, (#Type.basic as t), a) ->
      Vec.push ivec @@ ins @@ `load (x, t, op a)
    | `store ((#Type.basic as t), v, a) ->
      Vec.push ivec @@ ins @@ `store (t, op v, op a)
    | `load (x, `name _, _) ->
      Hashtbl.find env.unrefs x |>
      Option.iter ~f:(List.iter ~f:(Vec.push ivec))
    | `store (`name _, _, _) ->
      Hashtbl.find env.blits l |>
      Option.iter ~f:(List.iter ~f:(Vec.push ivec))

  let transl_call env ivec l f =
    let k = Hashtbl.find_exn env.calls l in
    (* Instructions before the call. *)
    Ftree.iter k.callai ~f:(Vec.push ivec);
    (* Register and memory arguments. *)
    let args = Ftree.to_list k.callar in
    (* The call itself. *)
    let c = `call (k.callrr, transl_global env f, args) in
    Vec.push ivec @@ Abi.Insn.create ~label:l c;
    (* Instructions after the call. *)
    Ftree.iter k.callri ~f:(Vec.push ivec)

  let transl_insn env ivec i =
    let l = Insn.label i in
    let ins = Abi.Insn.create ~label:l in
    match Insn.op i with
    | #Insn.basic as b ->
      Vec.push ivec @@
      ins (transl_basic env b :> Abi.Insn.op)
    | #Insn.mem as m -> transl_mem env ivec l m
    | `vastart _ ->
      Hashtbl.find_exn env.vastart l |>
      List.iter ~f:(Vec.push ivec)
    | `call (_, f, _, _) ->
      transl_call env ivec l f
    | `vaarg _ ->
      (* Should be handled in `transl_blk`. *)
      assert false

  let transl_swindex env = function
    | `var x -> `var (transl_var env x)
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

  let transl_ctrl t env l (c : ctrl) =
    let dst = transl_dst env in
    let is, c' = match c with
      | `hlt -> [], `hlt
      | `jmp d -> [], `jmp (dst d)
      | `br (c, y, n) -> [], `br (transl_var env c, dst y, dst n)
      | `sw (t, i, d, tbl) -> [], transl_sw env t i d tbl
      | `ret None -> [], `ret []
      | `ret Some _ -> transl_ret env l in
    t.cins <- is;
    t.ctrl <- c'

  (* We're done translating this block, either because we translated
     all the remaining instructions or we had to split it in the
     `vaarg` case. *)
  let commit_blk t label =
    List.iter t.cins ~f:(Vec.push t.ivec);
    let insns = Vec.to_list t.ivec in
    Vec.clear t.ivec;
    Vec.push t.bvec @@ Abi.Blk.create ()
      ~label ~insns ~args:t.args ~ctrl:t.ctrl

  (* Translate a single block, which may be split into multiple blocks. *)
  let rec transl_blk t env label s = match Seq.next s with
    | None ->
      commit_blk t label;
      let blks = Vec.to_list t.bvec in
      Vec.clear t.bvec;
      !!blks
    | Some (i, rest) -> match Insn.op i with
      | `vaarg _ ->
        (* If we performed the `vaarg` lowering pass beforehand, then
           this shouldn't fail. *)
        let v = Hashtbl.find_exn env.vaarg @@ Insn.label i in
        transl_vaarg t env label v rest
      | `uop (x, `uitof (ti, tf), a) ->
        transl_uitof t env label ti tf x a rest
      | _ ->
        (* No splitting needed. *)
        transl_insn env t.ivec i;
        transl_blk t env label rest

  (* Translate a `vaarg` instruction in the middle of a block. This is
     where we split it into multiple blocks and resume translating the
     rest of the instructions. *)
  and transl_vaarg t env label v rest =
    (* Jump to the start of the `vaarg` logic. *)
    let start = Abi.Blk.label @@ List.hd_exn v.vablks in
    let t' = {t with cins = []; ctrl = `jmp (`label (start, []))} in
    commit_blk t' label;
    (* Resume with the provided continuation. *)
    t.args <- [];
    List.iter v.vablks ~f:(Vec.push t.bvec);
    transl_blk t env v.vacont rest

  (* `uitof` requires us to do a bit of logic, since the hardware doesn't
     support it natively.

     XXX: it's possible to have this step delayed until right before
     instruction selection. However, all of the potential optimizations
     related to this instruction should've happened by now.
  *)
  and transl_uitof t env label ti tf x a rest =
    let a = transl_operand env a in
    match ti with
    | `i64 ->
      let* l1 = Context.Label.fresh in
      let* l2 = Context.Label.fresh in
      let* l3 = Context.Label.fresh in
      (* br (%a < 0) @l1 @l2 *)
      let* c, ci = Cv.Abi.binop (`slt ti) a (`int (Bv.zero, ti)) in
      let br = `br (c, `label (l1, []), `label (l2, [])) in
      let t' = {t with cins = [ci]; ctrl = br} in
      commit_blk t' label;
      t.args <- [];
      (* @l1:
           %sh = lsr.ti a, 1     ; divide by 2
           %an = and.ti a, 1     ; is `a` odd?
           %or_ = or.ti %sh, %an ; set LSB if `a` was odd
           %k = sitof.ti.tf %or_ ; convert to float
           %ad = add.tf %k, %k   ; now double it
           jmp @l3(%ad)
      *)
      let* sh, shi = Cv.Abi.binop (`lsr_ ti) a (`int (Bv.one, ti)) in
      let* an, ani = Cv.Abi.binop (`and_ ti) a (`int (Bv.one, ti)) in
      let* or_, ori = Cv.Abi.binop (`or_ ti) (`var sh) (`var an) in
      let* k, ki = Cv.Abi.unop (`sitof (ti, tf)) (`var or_) in
      let* ad, adi = Cv.Abi.binop (`add (tf :> Type.basic)) (`var k) (`var k) in
      let jmp = `jmp (`label (l3, [`var ad])) in
      let t' = {t with cins = [shi; ani; ori; ki; adi]; ctrl = jmp} in
      commit_blk t' l1;
      (* @l2:
           %k = sitof.ti.tf a
           jmp @l3(%k)
      *)
      let* k, ki = Cv.Abi.unop (`sitof (ti, tf)) a in
      let jmp = `jmp (`label (l3, [`var k])) in
      let t' = {t with cins = [ki]; ctrl = jmp} in
      commit_blk t' l2;
      (* @l3(%arg):
           x = copy %arg
      *)
      let* arg = Context.Var.fresh in
      let* cpyi = Cv.Abi.insn (`uop (x, `copy (tf :> Type.basic), `var arg)) in
      Vec.push t.ivec cpyi;
      t.args <- [arg];
      transl_blk t env l3 rest
    | _ ->
      let* ki = Cv.Abi.insn (`uop (x, `sitof (ti, tf), a)) in
      Vec.push t.ivec ki;
      transl_blk t env label rest

  let transl_blks env =
    let t = create_transl () in
    let entry = Func.entry env.fn in
    let bvec = Vec.create () in
    let+ () = Func.blks env.fn |> Context.Seq.iter ~f:(fun b ->
        let l = Blk.label b in
        (* Entry block copies the parameters. *)
        if Label.(l = entry) then
          Vec.iter env.params ~f:(fun p ->
              List.iter p.pins ~f:(Vec.push t.ivec));
        t.args <- Seq.to_list @@ Blk.args b;
        transl_ctrl t env l @@ Blk.ctrl b;
        let+ blks = transl_blk t env l @@ Blk.insns b in
        List.iter blks ~f:(Vec.push bvec)) in
    Vec.to_list bvec

  let make_dict env =
    let lnk = Func.linkage env.fn in
    let dict = Dict.singleton Func.Tag.linkage lnk in
    let dict = if Func.variadic env.fn
      then Dict.set dict Func.Tag.variadic ()
      else dict in
    dict

  let make_args env =
    let args =
      Vec.to_sequence_mutable env.params |>
      Seq.map ~f:(fun p -> p.pvar, p.pty) |>
      Seq.to_list in
    match env.alpar with
    | None -> args
    | Some r ->
      let arg = `reg (r, reg_str `rax) in
      (arg, `i8) :: args

  let go env =
    let slots = Func.slots env.fn |> Seq.to_list in
    let slots = slots @ Vec.to_list env.slots in
    let args = make_args env in
    let* blks = transl_blks env in
    let blks = match env.rsave with
      | Some r -> r.rsint :: r.rssse :: blks
      | None -> blks in
    let*? fn =
      Abi.Func.create () ~slots ~args ~blks
        ~name:(Func.name env.fn)
        ~dict:(make_dict env) in
    !!fn
end
