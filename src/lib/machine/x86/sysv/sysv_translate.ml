open Core
open Regular.Std
open Virtual
open Sysv_common

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
  | `var x -> `var (transl_var env x)
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
  | [] -> Ftree.to_list (acc @> commit_blk ivec args ctrl label)
  | i :: rest -> match Insn.op i with
    | `vaarg _ ->
      begin match Hashtbl.find env.vaarg @@ Insn.label i with
        | None -> transl_blk env ivec args ctrl label acc rest
        | Some v ->
          (* Jump to the start of the `vaarg` logic. *)
          let start = Abi.Blk.label @@ List.hd_exn v.vablks in
          let ctrl' = [], `jmp (`label (start, [])) in
          let b = commit_blk ivec args ctrl' label in
          (* Resume with the provided continuation. *)
          let acc = acc @>* (b :: v.vablks) in
          transl_blk env ivec [] ctrl v.vacont acc rest
      end
    | _ ->
      (* No splitting needed. *)
      transl_insn env ivec i;
      transl_blk env ivec args ctrl label acc rest

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
