(* Reify to our CFG representation. *)

open Core
open Extractor_core
open Regular.Std
open Graphlib.Std
open Virtual

open Context.Syntax

(* Maps IDs to generated temporaries. We use a persistent map
   because it is scoped to the current line in the dominator
   tree. This way, we can duplicate code when we find a partial
   redundancy. *)
type scp = (Var.t * Label.t) Id.Map.t

let empty_scp : scp = Id.Map.empty

type env = {
  insn        : Insn.op Label.Table.t;
  ctrl        : ctrl Label.Table.t;
  news        : Label.t Id.Map.t Label.Table.t;
  closure     : Label.Set.t Label.Table.t;
  mutable cur : Label.t;
}

let init () = {
  insn = Label.Table.create ();
  ctrl = Label.Table.create ();
  news = Label.Table.create();
  closure = Label.Table.create ();
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

let extract_label t l = match Hashtbl.find t.eg.lbl2id l with
  | None -> !!None
  | Some id -> match extract t id with
    | None -> extract_fail l @@ Common.find t.eg id
    | Some _ as e -> !!e

let upd t x y = Hashtbl.update t x ~f:(Option.value ~default:y)

let find_var t l = match Hashtbl.find t.eg.input.tbl l with
  | Some `insn (_, _, Some x) -> !!(x, l)
  | Some _ | None -> no_var l

let new_var env scp canon real = match Map.find !scp canon with
  | Some p -> !!p
  | None ->
    let* x = Context.Var.fresh in
    let+ l = Context.Label.fresh in
    scp := Map.set !scp ~key:canon ~data:(x, l);
    Hashtbl.update env.news env.cur ~f:(function
        | None -> Id.Map.singleton real l
        | Some m -> match Map.add m ~key:real ~data:l with
          | `Duplicate -> assert false
          | `Ok m -> m);
    x, l

let insn t env scp a f =
  let* x, l = match a with
    | Label l -> find_var t l
    | Id {canon; real} ->
      new_var env scp canon real in
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

let rec pure t env scp e : operand Context.t =
  let pure = pure t env scp in
  let insn = insn t env scp in
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
  | E (_, Ovaarg (x, _), [_]) -> !!(`var x)
  | E (_, Ovar x, []) -> !!(`var x)
  (* The rest are rejected. *)
  | E (_, Oaddr _, _)
  | E (_, Obinop _, _)
  | E (_, Obool _, _)
  | E (_, Obr, _)
  | E (_, Ocall0 _, _)
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
  | E (_, Ovaarg _, _)
  | E (_, Ovar _, _)
  | E (_, Ovastart _, _) -> invalid_pure e

and callargs t env scp = function
  | E (_, Ocallargs, args) ->
    Context.List.map args ~f:(pure t env scp)
  | e -> invalid_callargs e

and global t env scp e : global Context.t = match e with
  | E (_, Oaddr a, []) -> !!(`addr a)
  | E (_, Oaddr _, _) -> invalid_global e
  | E (_, Osym (s, o), []) -> !!(`sym (s, o))
  | E (_, Osym _, _) -> invalid_global e
  | _ -> pure t env scp e >>= function
    | `var x -> !!(`var x)
    | `int (i, _) -> !!(`addr i)
    | _ -> invalid_global e

let local t env scp l args =
  let+ args = Context.List.map args ~f:(pure t env scp) in
  l, args

let dst t env scp : ext -> dst Context.t = function
  | E (_, Olocal l, args) ->
    let+ l, args = local t env scp l args in
    `label (l, args)
  | e ->
    let+ g = global t env scp e in
    (g :> dst)

let table_elt t env scp : ext -> (Bv.t * local) Context.t = function
  | E (_, Otbl i, [E (_, Olocal l, args)]) ->
    let+ l, args = local t env scp l args in
    i, `label (l, args)
  | e -> invalid_tbl e

let table t env scp tbl ty =
  let* tbl = Context.List.map tbl ~f:(table_elt t env scp) in
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

let sw_default t env scp l = function
  | E (_, Olocal l', args) ->
    let+ l, args = local t env scp l' args in
    `label (l, args)
  | d -> invalid l d

let sw l e ty i d tbl = match i with
  | #Ctrl.swindex as i -> !!(`sw (ty, i, d, tbl))
  | `int (i, _) -> !!(`jmp (table_dst tbl i d))
  | _ -> invalid l e

let vaarg l e x t = function
  | (`var _ | `sym _) as a -> !!(`vaarg (x, t, a))
  | `int (a, _) -> !!(`vaarg (x, t, `addr a))
  | _ -> invalid l e

let vastart l e = function
  | (`var _ | `sym _) as a -> !!(`vastart a)
  | `int (a, _) -> !!(`vastart (`addr a))
  | _ -> invalid l e

let exp t env scp l e =
  let pure = pure t env scp in
  let dst = dst t env scp in
  let insn = insn' env l in
  let ctrl = ctrl env l in
  match e with
  (* Only canonical forms are accepted. *)
  | E (_, Obr, [c; y; n]) -> ctrl @@ fun () ->
    let* c = pure c in
    let* y = dst y in
    let* n = dst n in
    br l e c y n
  | E (_, Ocall0 _, [f; args; vargs]) -> insn @@ fun () ->
    let* f = global t env scp f in
    let* args = callargs t env scp args in
    let+ vargs = callargs t env scp vargs in
    `call (None, f, args, vargs)
  | E (_, Ocall (x, ty), [f; args; vargs]) -> insn @@ fun () ->
    let* f = global t env scp f in
    let* args = callargs t env scp args in
    let+ vargs = callargs t env scp vargs in
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
  | E (_, Ostore (t, _), [v; x]) -> insn @@ fun () ->
    let* v = pure v in
    let+ x = pure x in
    `store (t, v, x)
  | E (_, Osw ty, i :: d :: tbl) -> ctrl @@ fun () ->
    let* i = pure i in
    let* d = sw_default t env scp l d in
    let* tbl = table t env scp tbl ty in
    sw l e ty i d tbl
  | E (_, Ovaarg (x, t), [a]) -> insn @@ fun () ->
    let* a = pure a in
    vaarg l e x t a
  | E (_, Ovastart _, [a]) -> insn @@ fun () ->
    let* a = pure a in
    vastart l e a
  (* The rest are rejected. *)
  | E (_, Oaddr _, _)
  | E (_, Obinop _, _)
  | E (_, Obool _, _)
  | E (_, Obr, _)
  | E (_, Ocall0 _, _)
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
  | E (_, Ovaarg _, _)
  | E (_, Ovar _, _)
  | E (_, Ovastart _, _) -> invalid l e

let not_pseudo = Fn.non Label.is_pseudo
let descendants t = Tree.descendants t.eg.input.dom
let frontier t = Frontier.enum t.eg.input.df
let to_set = Fn.compose Label.Set.of_sequence @@ Seq.filter ~f:not_pseudo

let rec closure ?(self = true) t env l =
  let c = match Hashtbl.find env.closure l with
    | Some c -> c
    | None ->
      let c =
        frontier t l |> Seq.filter ~f:not_pseudo |>
        (* A block can be in its own dominance frontier, so
           we need to avoid an infinite loop. *)
        Seq.filter ~f:(Fn.non @@ Label.equal l) |>
        Seq.map ~f:(closure t env) |>
        Seq.fold ~init:(to_set @@ descendants t l) ~f:Set.union in
      Hashtbl.set env.closure ~key:l ~data:c;
      c in
  if self then Set.add c l else c

let post_dominated t l = Tree.is_ancestor_of t.eg.input.pdom ~child:l

let is_partial_redundancy t env l id =
  (* Ignore the results of LICM. *)
  not (Hash_set.mem t.eg.licm id) && begin
    (* Get the blocks associated with the labels that were
       "moved" for this node. *)
    let bs =
      Hashtbl.find_exn t.eg.imoved id |>
      Set.to_sequence |> Seq.map ~f:(fun l' ->
          match Hashtbl.find_exn t.eg.input.tbl l' with
          | `insn (_, b, _) -> Blk.label b
          | `blk _ -> assert false) in
    (* If one of these blocks post-dominates the block that we're
       moving to, then it is safe to allow the move to happen,
       since we are inevitably going to compute it. *)
    not (Seq.exists bs ~f:(post_dominated t l)) && begin
      (* For each of these blocks, get its reflexive transitive
         closure in the dominator tree, and union them together. *)
      let tc = Seq.fold bs ~init:Label.Set.empty ~f:(fun tc l ->
          Set.union tc @@ closure t env l) in
      (* Get the non-reflexive transitive closure of the block
         that we moved to. *)
      let ds = closure t env l ~self:false in
      (* If these sets are not equal, then we have a partial
         redundancy, and thus need to duplicate code. *)
      not @@ Label.Set.equal ds tc
    end
  end

let reify t env scp l =
  let* () = match Hashtbl.find t.eg.lmoved l with
    | None -> !!()
    | Some s ->
      (* Explore the newest nodes first. *)
      Set.to_sequence s ~order:`Decreasing |>
      Context.Seq.iter ~f:(fun id ->
          let id = Common.find t.eg id in
          match extract t id with
          | None -> extract_fail l id
          | Some e -> match e with
            | E (_, Obr, _)
            | E (_, Ojmp, _)
            | E (_, Oret, _)
            | E (_, Osw _, _)
            | E (_, Ocall0 _, _)
            | E (_, Ocall _, _)
            | E (_, Oload _, _)
            | E (_, Oset _, _)
            | E (_, Ostore _, _)
            | E (_, Ovaarg _, _)
            | E (_, Ovastart _, _) ->
              (* Ignore "effectful" operators that got moved; maybe we
                 can do something with the control-flow operators, but
                 I think it would be delicate to handle correctly. *)
              !!()
            | _ when is_partial_redundancy t env l id -> !!()
            | _ -> pure t env scp e >>| ignore) in
  extract_label t l >>= function
  | Some e -> exp t env scp l e
  | None -> !!()

let collect t l =
  let env = init () in
  let q = Stack.singleton (l, empty_scp) in
  let rec loop () = match Stack.pop q with
    | None -> !!env
    | Some (l, scp) ->
      env.cur <- l;
      let scp = ref scp in
      let* () = reify t env scp l in
      Tree.children t.eg.input.cdom l |>
      Seq.iter ~f:(fun l -> Stack.push q (l, !scp));
      loop () in
  loop ()

let find_insn env l =
  Hashtbl.find env.insn l |> Option.map ~f:(Insn.create ~label:l)

let find_news ?(rev = false) env l =
  let order = if rev then `Decreasing_key else `Increasing_key in
  Hashtbl.find env.news l |>
  Option.value_map ~default:[] ~f:(fun m ->
      Map.to_sequence ~order m |> Seq.map ~f:snd |>
      Seq.filter_map ~f:(find_insn env) |> Seq.to_list)

let cfg t =
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
            let i = match find_insn env label with
              | Some i' -> Insn.with_dict i' @@ Insn.dict i
              | None -> i in
            let news = find_news env label ~rev:true in
            List.rev_append news (i :: acc)) in
      Blk.create () ~insns ~ctrl ~label
        ~args:(Blk.args b |> Seq.to_list)
        ~dict:(Blk.dict b))
