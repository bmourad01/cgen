(* Reify to our CFG representation. *)

open Core
open Extractor_core
open Regular.Std
open Graphlib.Std
open Virtual

open Context.Syntax

type env = {
  insn        : Insn.op Label.Table.t;
  ctrl        : ctrl Label.Table.t;
  temp        : (Var.t * Label.t) Id.Table.t;
  news        : Label.t list Label.Table.t;
  mutable cur : Label.t;
}

let init () = {
  insn = Label.Table.create ();
  ctrl = Label.Table.create ();
  temp = Id.Table.create ();
  news = Label.Table.create();
  cur = Label.pseudoentry;
}

let extract_fail l id =
  Context.fail @@ Error.createf
    "Couldn't extract term for label %a (id %a)"
    Label.pps l Id.pps id

let invalid l e =
  Context.fail @@ Error.createf
    "Invalid term %a for label %a"
    pps_ext e Label.pps l

let invalid_pure e =
  Context.fail @@ Error.createf "Invalid pure term %a" pps_ext e

let invalid_callargs e =
  Context.fail @@ Error.createf "Invalid callargs term %a" pps_ext e

let invalid_global e =
  Context.fail @@ Error.createf "Invalid global term %a" pps_ext e

let invalid_tbl e =
  Context.fail @@ Error.createf "Invalid table term %a" pps_ext e

let no_var l =
  Context.fail @@ Error.createf
    "No variable is bound for label %a"
    Label.pps l

let extract t l = match Hashtbl.find t.eg.lbl2id l with
  | None -> !!None
  | Some id ->
    let id = Common.find t.eg id in
    match extract t id with
    | None -> extract_fail l id
    | Some _ as e -> !!e

let upd t x y = Hashtbl.update t x ~f:(Option.value ~default:y)

let find_var t l = match Hashtbl.find t.eg.input.tbl l with
  | Some `insn (_, _, Some x) -> !!(x, l)
  | Some _ | None -> no_var l

let new_var env id = match Hashtbl.find env.temp id with
  | Some p -> !!p
  | None ->
    let* l = Context.Label.fresh in
    let+ x = Context.Var.fresh in
    Hashtbl.set env.temp ~key:id ~data:(x, l);
    Hashtbl.add_multi env.news ~key:env.cur ~data:l;
    x, l

let insn t env a f =
  let* x, l = match a with
    | Label l -> find_var t l
    | Id id -> new_var env id in
  let+ op = f x in
  upd env.insn l op;
  `var x

let insn' env l f =
  let+ op = f () in
  upd env.insn l op

let ctrl env l f =
  let+ c = f () in
  upd env.ctrl l c

let sel e x ty c y n = match c with
  | `var c -> !!(`sel (x, ty, c, y, n))
  | _ -> invalid_pure e

let rec pure t env e : operand Context.t =
  let pure = pure t env in
  let insn = insn t env in
  match e with
  (* Only canonical forms are accepted. *)
  | E (a, Obinop b, [l; r]) -> insn a @@ fun x ->
    let* l = pure l in
    let+ r = pure r in
    `bop (x, b, l, r)
  | E (_, Obool b, []) -> !!(`bool b)
  | E (_, Ocall (x, _), _) -> !!(`var x)
  | E (_, Odouble d, []) -> !!(`double d)
  | E (_, Oint (i, t), []) -> !!(`int (i, t))
  | E (_, Oload (x, _), _) -> !!(`var x)
  | E (a, Osel ty, [c; y; n]) -> insn a @@ fun x ->
    let* c = pure c in
    let* y = pure y in
    let* n = pure n in
    sel e x ty c y n
  | E (_, Osingle s, []) -> !!(`float s)
  | E (_, Osym (s, n), []) -> !!(`sym (s, n))
  | E (a, Ounop u, [y]) -> insn a @@ fun x ->
    let+ y = pure y in
    `uop (x, u, y)
  | E (_, Ovar x, []) -> !!(`var x)
  (* The rest are rejected. *)
  | E (_, Oaddr _, _)
  | E (_, Obinop _, _)
  | E (_, Obool _, _)
  | E (_, Obr, _)
  | E (_, Ocall0, _)
  | E (_, Ocallargs, _)
  | E (_, Odouble _, _)
  | E (_, Ojmp, _)
  | E (_, Oint _, _)
  | E (_, Olocal _, _)
  | E (_, Oret, _)
  | E (_, Osel _, _)
  | E (_, Oset _, _)
  | E (_, Osingle _, _)
  | E (_, Ostore _, _)
  | E (_, Osw _, _)
  | E (_, Osym _, _)
  | E (_, Otbl _, _)
  | E (_, Ounop _, _)
  | E (_, Ovar _, _) -> invalid_pure e

and callargs t env = function
  | E (_, Ocallargs, args) -> Context.List.map args ~f:(pure t env)
  | e -> invalid_callargs e

and global t env e : global Context.t = match e with
  | E (_, Oaddr a, []) -> !!(`addr a)
  | E (_, Oaddr _, _) -> invalid_global e
  | E (_, Osym (s, 0), []) -> !!(`sym s)
  | E (_, Osym _, _) -> invalid_global e
  | _ -> pure t env e >>= function
    | `var x -> !!(`var x)
    | `int (i, _) -> !!(`addr i)
    | _ -> invalid_global e

let local t env l args =
  let+ args = Context.List.map args ~f:(pure t env) in
  l, args

let dst t env : ext -> dst Context.t = function
  | E (_, Olocal l, args) ->
    let+ l, args = local t env l args in
    `label (l, args)
  | e ->
    let+ g = global t env e in
    (g :> dst)

let table_elt t env : ext -> (Bv.t * local) Context.t = function
  | E (_, Otbl i, [E (_, Olocal l, args)]) ->
    let+ l, args = local t env l args in
    i, `label (l, args)
  | e -> invalid_tbl e 

let table t env tbl ty =
  let* tbl = Context.List.map tbl ~f:(table_elt t env) in
  let*? x = Ctrl.Table.create tbl ty in
  !!x

let table_dst tbl i d =
  Ctrl.Table.find tbl i |>
  Option.value ~default:d |> fun l ->
  (l :> dst)

(* Ideally this would be captured in our rewrite rules. *)
let br l e c y n = match c with
  | `bool f -> !!(`jmp (if f then y else n))
  | `var _ when equal_dst y n -> !!(`jmp y)
  | `var c -> !!(`br (c, y, n))
  | _ -> invalid l e

let sw_default t env l = function
  | E (_, Olocal l', args) ->
    let+ l, args = local t env l' args in
    `label (l, args)
  | d -> invalid l d

let sw l e ty i d tbl = match i with
  | #Ctrl.swindex as i -> !!(`sw (ty, i, d, tbl))
  | `int (i, _) -> !!(`jmp (table_dst tbl i d))
  | _ -> invalid l e

let exp t env l e =
  let pure = pure t env in
  let dst = dst t env in
  let insn = insn' env l in
  let ctrl = ctrl env l in
  match e with
  (* Only canonical forms are accepted. *)
  | E (_, Obr, [c; y; n]) -> ctrl @@ fun () ->
    let* c = pure c in
    let* y = dst y in
    let* n = dst n in
    br l e c y n
  | E (_, Ocall0, [f; args; vargs]) -> insn @@ fun () ->
    let* f = global t env f in
    let* args = callargs t env args in
    let+ vargs = callargs t env vargs in
    `call (None, f, args, vargs)
  | E (_, Ocall (x, ty), [f; args; vargs]) -> insn @@ fun () ->
    let* f = global t env f in
    let* args = callargs t env args in
    let+ vargs = callargs t env vargs in
    `call (Some (x, ty), f, args, vargs)
  | E (_, Oload (x, t), [y]) -> insn @@ fun () ->
    let+ y = pure y in
    `load (x, t, y)
  | E (_, Ojmp, [d]) -> ctrl @@ fun () ->
    let+ d = dst d in
    `jmp d
  | E (_, Oret, [x]) -> ctrl @@ fun () ->
    let+ x = pure x in
    `ret (Some x)
  | E (_, Oset _, [y]) -> pure y >>| ignore
  | E (_, Ostore t, [v; x]) -> insn @@ fun () ->
    let* v = pure v in
    let+ x = pure x in
    `store (t, v, x)
  | E (_, Osw ty, i :: d :: tbl) -> ctrl @@ fun () ->
    let* i = pure i in
    let* d = sw_default t env l d in
    let* tbl = table t env tbl ty in
    sw l e ty i d tbl
  (* The rest are rejected. *)
  | E (_, Oaddr _, _)
  | E (_, Obinop _, _)
  | E (_, Obool _, _)
  | E (_, Obr, _)
  | E (_, Ocall0, _)
  | E (_, Ocall _, _)
  | E (_, Ocallargs, _)
  | E (_, Odouble _, _)
  | E (_, Ojmp, _)
  | E (_, Oint _, _)
  | E (_, Oload _, _)
  | E (_, Olocal _, _)
  | E (_, Oret, _)
  | E (_, Osel _, _)
  | E (_, Oset _, _)
  | E (_, Osingle _, _)
  | E (_, Ostore _, _)
  | E (_, Osw _, _)
  | E (_, Osym _, _)
  | E (_, Otbl _, _)
  | E (_, Ounop _, _)
  | E (_, Ovar _, _) -> invalid l e

let collect t l =
  let env = init () in
  let q = Queue.singleton l in
  let rec loop () = match Queue.dequeue q with
    | None -> !!env
    | Some l ->
      env.cur <- l;
      let* () = extract t l >>= function
        | Some e -> exp t env l e
        | None -> !!() in
      Tree.children t.eg.input.dom l |>
      Seq.iter ~f:(Queue.enqueue q);
      loop () in
  loop ()

let find_insn env l =
  Hashtbl.find env.insn l |>
  Option.map ~f:(fun o -> Insn.create o ~label:l)

let find_news env l =
  Hashtbl.find env.news l |>
  Option.value_map ~default:[]
    ~f:(List.filter_map ~f:(find_insn env))

let reify t =
  let+ env = collect t Label.pseudoentry in
  Func.map_blks t.eg.input.fn ~f:(fun b ->
      let label = Blk.label b in
      let ctrl = match Hashtbl.find env.ctrl label with
        | None -> Blk.ctrl b
        | Some c -> c in
      let insns =
        Blk.insns b ~rev:true |>
        Seq.fold ~init:(find_news env label) ~f:(fun acc i ->
            let label = Insn.label i in
            let i = find_insn env label |> Option.value ~default:i in
            find_news env label @ (i :: acc)) in
      Blk.create () ~insns ~ctrl ~label
        ~args:(Blk.args b |> Seq.to_list))
