open Core
open Graphlib.Std
open Regular.Std
open Common

type cost = child:(id -> int) -> enode -> int

type prov =
  | Label of Label.t
  | Id of id

(* We'll use an intermediate data structure to extract back to our real
   expression tree representation. *)
type ext = E of prov * Enode.op * ext list

let rec pp_ext ppf = function
  | E (_, op, args) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)" Enode.pp_op op
      (Format.pp_print_list ~pp_sep pp_ext) args

let pps_ext () e = Format.asprintf "%a" pp_ext e

type t = {
  eg          : egraph;
  cost        : cost;
  table       : (int * enode) Id.Table.t;
  memo        : ext Id.Table.t;
  mutable ver : int;
  mutable sat : bool;
}

let init eg ~cost = {
  eg;
  cost;
  table = Id.Table.create ();
  memo = Id.Table.create ();
  ver = eg.ver;
  sat = false;
}

let id_cost t id = match Hashtbl.find t.table @@ find t.eg id with
  | None -> failwithf "Couldn't calculate cost for node id %a" Id.pps id ()
  | Some (c, _) -> c

let has_cost t n =
  Enode.children n |> List.for_all ~f:(Hashtbl.mem t.table)

let node_cost t n =
  if not @@ has_cost t n then None
  else Some (t.cost ~child:(id_cost t) n, n)

(* Find the least-expensive term. *)
let best_term t ns =
  Vec.fold ns ~init:None ~f:(fun acc n ->
      node_cost t n |> Option.merge acc
        ~f:(fun ((c1, _) as a) ((c2, _) as b) ->
            if c2 < c1 then b else a))

(* Saturate the cost table. *)
let rec saturate t (cs : classes) =
  t.sat <- true;
  Hashtbl.iteri cs ~f:(fun ~key:id ~data:ns ->
      match Hashtbl.find t.table id, best_term t ns with
      | None, Some term ->
        Hashtbl.set t.table ~key:id ~data:term;
        t.sat <- false
      | Some (x, _), Some ((y, _) as term) when y < x ->
        Hashtbl.set t.table ~key:id ~data:term;
        t.sat <- false
      | _ -> ());
  if not t.sat then saturate t cs

(* Check if the underlying e-graph has been updated. If so, we should
   re-compute the costs for each node. *)
let check t = if t.ver <> t.eg.ver then begin
    Hashtbl.clear t.table;
    Hashtbl.clear t.memo;
    t.ver <- t.eg.ver;
    t.sat <- false;
  end

(* Extract the intermediate form to our expression tree representation,
   making it easy for a user of this API to inspect and match on terms
   that we derived from the CFG representation. *)
module Term = struct
  open O.Let

  let lbl = function
    | Label l -> Some l
    | Id _ -> None

  let rec pure = function
    (* Only canonical forms are accepted. *)
    | E (a, Oalloc n, []) -> Some (Exp.Palloc (lbl a, n))
    | E (a, Obinop b, [l; r]) ->
      let+ l = pure l and+ r = pure r in
      Exp.Pbinop (lbl a, b, l, r)
    | E (_, Obool b, []) -> Some (Exp.Pbool b)
    | E (a, Ocall t, [f; args; vargs]) ->
      let+ f = global f
      and+ args = callargs args
      and+ vargs = callargs vargs in
      Exp.Pcall (lbl a, t, f, args, vargs)
    | E (_, Odouble d, []) -> Some (Exp.Pdouble d)
    | E (_, Oint (i, t), []) -> Some (Exp.Pint (i, t))
    | E (a, Oload t, [x]) ->
      let+ x = pure x in
      Exp.Pload (lbl a, t, x)
    | E (a, Osel t, [c; y; n]) ->
      let+ c = pure c and+ y = pure y and+ n = pure n in
      Exp.Psel (lbl a, t, c, y, n)
    | E (_, Osingle s, []) -> Some (Exp.Psingle s)
    | E (_, Osym (s, n), []) -> Some (Exp.Psym (s, n))
    | E (a, Ounop u, [x]) ->
      let+ x = pure x in
      Exp.Punop (lbl a, u, x)
    | E (_, Ovar x, []) -> Some (Exp.Pvar x)
    (* The rest are rejected. *)
    | E (_, Oaddr _, _)
    | E (_, Oalloc _, _)
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
    | E (_, Ovar _, _) -> None

  and callargs = function
    | E (_, Ocallargs, args) -> O.List.map args ~f:pure
    | _ -> None

  and global = function
    | E (_, Oaddr a, []) -> Some (Exp.Gaddr a)
    | E (_, Oaddr _, _) -> None
    | E (_, Osym (s, 0), []) -> Some (Exp.Gsym s)
    | E (_, Osym _, _) -> None
    | e ->
      let+ p = pure e in
      Exp.Gpure p

  let local l args =
    let+ args = O.List.map args ~f:pure in
    l, args

  let dst = function
    | E (_, Olocal l, args) ->
      let+ l = local l args in
      Exp.Dlocal l
    | e ->
      let+ g = global e in
      Exp.Dglobal g

  let table = function
    | E (_, Otbl i, [E (_, Olocal l, args)]) ->
      let+ l = local l args in
      i, l
    | _ -> None

  let exp = function
    (* Only canonical forms are accepted. *)
    | E (_, Obr, [c; y; n]) ->
      let+ c = pure c and+ y = dst y and+ n = dst n in
      Exp.Ebr (c, y, n)
    | E (_, Ocall0, [f; args; vargs]) ->
      let+ f = global f
      and+ args = callargs args
      and+ vargs = callargs vargs in
      Exp.Ecall (f, args, vargs)
    | E (_, Ojmp, [d]) ->
      let+ d = dst d in
      Exp.Ejmp d
    | E (_, Oret, [x]) ->
      let+ x = pure x in
      Exp.Eret x
    | E (_, Oset x, [y]) ->
      let+ y = pure y in
      Exp.Eset (x, y)
    | E (_, Ostore t, [v; x]) ->
      let+ v = pure v and+ x = pure x in
      Exp.Estore (t, v, x)
    | E (_, Osw t, i :: d :: tbl) ->
      let+ i = pure i
      and+ d = match d with
        | E (_, Olocal l, args) -> local l args
        | _ -> None
      and+ tbl = O.List.map tbl ~f:table in
      Exp.Esw (t, i, d, tbl)
    (* The rest are rejected. *)
    | E (_, Oaddr _, _)
    | E (_, Oalloc _, _)
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
    | E (_, Ovar _, _) -> None
end

(* Extract to our intermediate form and cache the results. *)
let rec extract_aux t id =
  let id = find t.eg id in
  match Hashtbl.find t.memo id with
  | Some _ as e -> e
  | None ->
    let open O.Let in
    let* _, n = Hashtbl.find t.table id in
    let+ cs = Enode.children n |> O.List.map ~f:(extract_aux t) in
    let p = match Hashtbl.find t.eg.id2lbl id with
      | Some l -> Label l
      | None -> Id id in
    let e = E (p, Enode.op n, cs) in
    Hashtbl.set t.memo ~key:id ~data:e;
    e

let extract t id =
  check t;
  if not t.sat then saturate t @@ eclasses t.eg;
  extract_aux t id

let term_exn t l = match Hashtbl.find t.eg.lbl2id l with
  | None -> None
  | Some id ->
    let id = find t.eg id in
    match extract t id with
    | None ->
      invalid_argf "Couldn't extract term for label %a (id %a)"
        Label.pps l Id.pps id ()
    | Some e -> match Term.exp e with
      | Some _ as e -> e
      | None ->
        invalid_argf
          "Term for label %a (id %a) is not well-formed: %a"
          Label.pps l Id.pps id pps_ext e ()

let term t l = Or_error.try_with @@ fun () -> term_exn t l

module Reify = struct
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
      let id = find t.eg id in
      match extract t id with
      | None -> extract_fail l id
      | Some _ as e -> !!e

  let upd t x y = Hashtbl.update t x ~f:(Option.value ~default:y)

  let insn t env a f =
    let* x, l = match a with
      | Label l ->
        begin match Hashtbl.find t.eg.input.tbl l with
          | Some `insn (_, _, Some x) -> !!(x, l)
          | Some _ | None -> no_var l
        end
      | Id id -> match Hashtbl.find env.temp id with
        | Some p -> !!p
        | None ->
          let* l = Context.Label.fresh in
          let+ x = Context.Var.fresh in
          Hashtbl.set env.temp ~key:id ~data:(x, l);
          Hashtbl.add_multi env.news ~key:env.cur ~data:l;
          x, l in
    let+ op = f x in
    upd env.insn l op;
    `var x

  let insn' env l f =
    let+ op = f () in
    upd env.insn l op

  let ctrl env l f =
    let+ c = f () in
    upd env.ctrl l c

  let rec pure t env e : operand Context.t =
    let pure = pure t env in
    let insn = insn t env in
    match e with
    (* Only canonical forms are accepted. *)
    | E (a, Oalloc n, []) -> insn a @@ fun x ->
      !!(`alloc (x, n))
    | E (a, Obinop b, [l; r]) -> insn a @@ fun x ->
      let+ l = pure l and+ r = pure r in
      `bop (x, b, l, r)
    | E (_, Obool b, []) -> !!(`bool b)
    | E (a, Ocall ty, [f; args; vargs]) -> insn a @@ fun x ->
      let+ f = global t env f
      and+ args = callargs t env args
      and+ vargs = callargs t env vargs in
      `call (Some (x, ty), f, args, vargs)
    | E (_, Odouble d, []) -> !!(`double d)
    | E (_, Oint (i, t), []) -> !!(`int (i, t))
    | E (a, Oload ty, [y]) -> insn a @@ fun x ->
      let+ y = pure y in
      `load (x, ty, y)
    | E (a, Osel ty, [c; y; n]) -> insn a @@ fun x ->
      let* y = pure y and* n = pure n in
      begin pure c >>= function
        | `var c -> !!(`sel (x, ty, c, y, n))
        | _ -> invalid_pure e
      end
    | E (_, Osingle s, []) -> !!(`float s)
    | E (_, Osym (s, n), []) -> !!(`sym (s, n))
    | E (a, Ounop u, [y]) -> insn a @@ fun x ->
      let+ y = pure y in
      `uop (x, u, y)
    | E (_, Ovar x, []) -> !!(`var x)
    (* The rest are rejected. *)
    | E (_, Oaddr _, _)
    | E (_, Oalloc _, _)
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

  let exp t env l e =
    let pure = pure t env in
    let dst = dst t env in
    let insn = insn' env l in
    let ctrl = ctrl env l in
    match e with
    (* Only canonical forms are accepted. *)
    | E (_, Obr, [c; y; n]) -> ctrl @@ fun () ->
      let* y = dst y and* n = dst n in
      begin pure c >>= function
        | `bool f -> !!(`jmp (if f then y else n))
        | `var _ when equal_dst y n -> !!(`jmp y)
        | `var c -> !!(`br (c, y, n))
        | _ -> invalid l e
      end
    | E (_, Ocall0, [f; args; vargs]) -> insn @@ fun () ->
      let+ f = global t env f
      and+ args = callargs t env args
      and+ vargs = callargs t env vargs in
      `call (None, f, args, vargs)
    | E (_, Ojmp, [d]) -> ctrl @@ fun () ->
      let+ d = dst d in
      `jmp d
    | E (_, Oret, [x]) -> ctrl @@ fun () ->
      let+ x = pure x in
      `ret (Some x)
    | E (_, Oset _, [y]) -> pure y >>| ignore
    | E (_, Ostore t, [v; x]) -> insn @@ fun () ->
      let+ v = pure v and+ x = pure x in
      `store (t, v, x)
    | E (_, Osw ty, i :: d :: tbl) -> ctrl @@ fun () ->
      let* d = match d with
        | E (_, Olocal l', args) ->
          let+ l, args = local t env l' args in
          (`label (l, args) :> local)
        | _ -> invalid l d
      and* tbl = table t env tbl ty in
      begin pure i >>= function
        | (`var _ | `sym _) as i -> !!(`sw (ty, i, d, tbl))
        | `int (i, _) -> !!(`jmp (table_dst tbl i d))
        | _ -> invalid l i
      end
    (* The rest are rejected. *)
    | E (_, Oaddr _, _)
    | E (_, Oalloc _, _)
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
    (* Traverse the tree breadth-first. *)
    let q = Queue.singleton l in
    let rec loop () = match Queue.dequeue q with
      | None -> !!env
      | Some l ->
        env.cur <- l;
        let* () = extract t l >>= function
          | Some e -> exp t env l e
          | None -> !!() in
        Tree.children t.eg.input.dom l |> Seq.iter ~f:(Queue.enqueue q);
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
    let open Context.Syntax in
    let+ env = collect t Label.pseudoentry in
    let fn = t.eg.input.fn in
    Func.blks fn |> Seq.map ~f:(fun b ->
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
          ~args:(Blk.args b |> Seq.to_list)) |>
    Seq.to_list |> Func.update_blks fn
end

let reify = Reify.reify
