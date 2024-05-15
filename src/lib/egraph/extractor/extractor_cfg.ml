(* Reify to our CFG representation. *)

open Core
open Extractor_core
open Regular.Std
open Graphlib.Std
open Virtual

module Common = Egraph_common
module Lset = Label.Tree_set
module Id = Egraph_id

open Context.Syntax

(* Maps IDs to generated temporaries. We use a persistent map
   because it is scoped to the current line in the dominator
   tree. This way, we can duplicate code when we find a partial
   redundancy. *)
type scope = (Var.t * Label.t) Id.Tree.t

let empty_scope : scope = Id.Tree.empty

type env = {
  insn        : Insn.op Label.Table.t;
  ctrl        : ctrl Label.Table.t;
  news        : Label.t Id.Tree.t Label.Table.t;
  closure     : Lset.t Label.Table.t;
  mutable cur : Label.t;
  mutable scp : scope;
}

let init () = {
  insn = Label.Table.create ();
  ctrl = Label.Table.create ();
  news = Label.Table.create();
  closure = Label.Table.create ();
  cur = Label.pseudoentry;
  scp = empty_scope;
}

let error_prefix = "In Extractor_cfg"

let extract_fail l id =
  Context.failf "%s: couldn't extract term for label %a (id %a)"
    error_prefix Label.pp l Id.pp id ()

let invalid l e =
  Context.failf "%s: invalid term %a for label %a"
    error_prefix pp_ext e Label.pp l ()

let invalid_pure e =
  Context.failf "%s: invalid pure term %a"
    error_prefix pp_ext e ()

let invalid_callargs e =
  Context.failf "%s: invalid callargs term %a"
    error_prefix pp_ext e ()

let invalid_global e =
  Context.failf "%s: invalid global term %a"
    error_prefix pp_ext e ()

let invalid_tbl e =
  Context.failf "%s: invalid table term %a"
    error_prefix pp_ext e ()

let no_var l =
  Context.failf "%s: no variable is bound for label %a"
    error_prefix Label.pp l ()

let extract_label t l = match Hashtbl.find t.eg.lval l with
  | None -> !!None
  | Some id -> match extract t id with
    | None -> extract_fail l @@ Common.find t.eg id
    | Some (E (Id {canon; _}, _, _)) when not @@ Hash_set.mem t.impure canon ->
      (* There may be an opportunity to "sink" this instruction,
         which is the dual of the "hoisting" optimization below.
         Since this is a pure operation, we can wait until it is
         actually needed by an effectful instruction or for
         control-flow. *)
      !!None
    | Some _ as e -> !!e

let upd t x y = Hashtbl.update t x ~f:(Option.value ~default:y)

let find_var t l = match Resolver.resolve t.eg.input.reso l with
  | Some `insn (_, _, Some x, _) -> !!(x, l)
  | Some _ | None -> no_var l

let new_var env canon real =
  match Id.Tree.find env.scp canon with
  | Some p -> !!p
  | None ->
    let* x = Context.Var.fresh in
    let+ l = Context.Label.fresh in
    env.scp <- Id.Tree.set env.scp ~key:canon ~data:(x, l);
    Hashtbl.update env.news env.cur ~f:(function
        | None -> Id.Tree.singleton real l
        | Some m -> match Id.Tree.add m ~key:real ~data:l with
          | `Duplicate -> assert false
          | `Ok m -> m);
    x, l

let insn t env a f =
  let* x, l = match a with
    | Label l -> find_var t l
    | Id {canon; real} ->
      new_var env canon real in
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
  | `bool true -> !!(`uop (x, `copy ty, y))
  | `bool false -> !!(`uop (x, `copy ty, n))
  | _ -> invalid_pure e

let rec pure t env e : operand Context.t =
  let pure = pure t env in
  let insn = insn t env in
  match e with
  (* Only canonical forms are accepted. *)
  | E (a, Obinop b, [l; r]) ->
    let* l = pure l in
    let* r = pure r in
    insn a @@ fun x ->
    !!(`bop (x, b, l, r))
  | E (_, Obool b, []) -> !!(`bool b)
  | E (_, Ocall (x, _), _) -> !!(`var x)
  | E (_, Odouble d, []) -> !!(`double d)
  | E (_, Oint (i, t), []) -> !!(`int (i, t))
  | E (_, Oload (x, _), _) -> !!(`var x)
  | E (a, Osel ty, [c; y; n]) ->
    let* c = pure c in
    let* y = pure y in
    let* n = pure n in
    insn a @@ fun x ->
    sel e x ty c y n
  | E (_, Osingle s, []) -> !!(`float s)
  | E (_, Osym (s, n), []) -> !!(`sym (s, n))
  | E (a, Ounop u, [y]) ->
    let* y = pure y in
    insn a @@ fun x ->
    !!(`uop (x, u, y))
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

let callargs t env = function
  | E (_, Ocallargs, args) ->
    Context.List.map args ~f:(pure t env)
  | e -> invalid_callargs e

let global t env e : global Context.t = match e with
  | E (_, Oaddr a, []) -> !!(`addr a)
  | E (_, Oaddr _, _) -> invalid_global e
  | E (_, Osym (s, o), []) -> !!(`sym (s, o))
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

let vaarg l e x t = function
  | (`var _ | `sym _) as a -> !!(`vaarg (x, t, a))
  | `int (a, _) -> !!(`vaarg (x, t, `addr a))
  | _ -> invalid l e

let vastart l e = function
  | (`var _ | `sym _) as a -> !!(`vastart a)
  | `int (a, _) -> !!(`vastart (`addr a))
  | _ -> invalid l e

let exp t env l e =
  let pure = pure t env in
  let dst = dst t env in
  let insn = insn' env l in
  let ctrl = ctrl env l in
  match e with
  (* Only canonical forms are accepted. *)
  | E (_, Obr, [c; y; n]) ->
    let* c = pure c in
    let* y = dst y in
    let* n = dst n in
    ctrl @@ fun () ->
    br l e c y n
  | E (_, Ocall0 _, [f; args; vargs]) ->
    let* f = global t env f in
    let* args = callargs t env args in
    let* vargs = callargs t env vargs in
    insn @@ fun () ->
    !!(`call (None, f, args, vargs))
  | E (_, Ocall (x, ty), [f; args; vargs]) ->
    let* f = global t env f in
    let* args = callargs t env args in
    let* vargs = callargs t env vargs in
    insn @@ fun () ->
    !!(`call (Some (x, ty), f, args, vargs))
  | E (_, Oload (x, t), [y]) ->
    let* y = pure y in
    insn @@ fun () ->
    !!(`load (x, t, y))
  | E (_, Ojmp, [d]) ->
    let* d = dst d in
    ctrl @@ fun () ->
    !!(`jmp d)
  | E (_, Oret, [x]) ->
    let* x = pure x in
    ctrl @@ fun () ->
    !!(`ret (Some x))
  | E (_, Oset _, [y]) -> pure y >>| ignore
  | E (_, Ostore (t, _), [v; x]) ->
    let* v = pure v in
    let* x = pure x in
    insn @@ fun () ->
    !!(`store (t, v, x))
  | E (_, Osw ty, i :: d :: tbl) ->
    let* i = pure i in
    let* d = sw_default t env l d in
    let* tbl = table t env tbl ty in
    ctrl @@ fun () ->
    sw l e ty i d tbl
  | E (_, Ovaarg (x, t), [a]) ->
    let* a = pure a in
    insn @@ fun () ->
    vaarg l e x t a
  | E (_, Ovastart _, [a]) ->
    let* a = pure a in
    insn @@ fun () ->
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

module Hoisting = struct
  let (++) = Lset.union
  let not_pseudo = Fn.non Label.is_pseudo
  let descendants t = Tree.descendants t.eg.input.dom
  let ancestors t = Tree.ancestors t.eg.input.pdom
  let frontier t = Frontier.enum t.eg.input.df
  let to_set = Fn.compose Lset.of_sequence @@ Seq.filter ~f:not_pseudo

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
          Seq.fold ~init:(to_set @@ descendants t l) ~f:(++) in
        Hashtbl.set env.closure ~key:l ~data:c;
        c in
    if self then Lset.add c l else Lset.remove c l

  (* Try the real ID first before moving on to the canonical ID. This could
     happen if we rescheduled a newer term before we unioned it with an older
     term. *)
  let find_moved t id cid =
    match Hashtbl.find t.eg.imoved id with
    | Some s -> s
    | None ->
      assert (id <> cid);
      match Hashtbl.find t.eg.imoved cid with
      | Some s -> s
      | None -> assert false

  let moved_blks t id cid =
    find_moved t id cid |> Label.Set.map ~f:(fun l ->
        match Resolver.resolve t.eg.input.reso l with
        | Some `insn (_, b, _, _) -> Blk.label b
        | Some `blk _ | None -> assert false)

  (* When we "move" duplicate nodes up to the LCA (lowest common ancestor)
     in the dominator tree, we might be introducing a partial redundancy.
     This means that, at the LCA, the node is not going to be used on all
     paths that are dominated by it, so we need to do a simple analysis to
     see if this is the case. *)
  let is_partial_redundancy t env l id cid =
    (* Ignore the results of LICM. Note that we do not use the canonical ID
       here, since we do our analysis before rewriting. *)
    not (Hash_set.mem t.eg.licm id) && begin
      (* Get the blocks associated with the labels that were
         "moved" for this node. *)
      let bs = moved_blks t id cid in
      (* If one of these blocks post-dominates the block that we're
         moving to, then it is safe to allow the move to happen,
         since we are inevitably going to compute it. However, this
         choice has a drawback in that it may extend the live range
         of this node beyond any benefit from hoisting it. In terms
         of native code generation, this means added register pressure,
         which may lead to increased spilling. *)
      let ans = to_set @@ ancestors t l in
      not (Set.exists bs ~f:(Lset.mem ans)) && begin
        (* For each of these blocks, get its reflexive transitive
           closure in the dominator tree, and union them together. *)
        let a = Set.fold bs ~init:Lset.empty
            ~f:(fun acc l -> acc ++ closure t env l) in
        (* Get the non-reflexive transitive closure of the block
           that we moved to. *)
        let b = closure t env l ~self:false in
        (* If these sets are not equal, then we have a partial
           redundancy, and thus need to duplicate code. *)
        not @@ Lset.equal a b
      end
    end

  (* If any nodes got moved up to this label, then we should check
     to see if it is eligible for this code motion optimization. *)
  let process_moved_nodes t env l =
    match Hashtbl.find t.eg.lmoved l with
    | None -> !!()
    | Some s ->
      (* Explore the newest nodes first. *)
      Set.to_sequence s ~order:`Decreasing |>
      Context.Seq.iter ~f:(fun id -> match extract t id with
          | None -> extract_fail l id
          | Some e ->
            let cid = Common.find t.eg id in
            if Hash_set.mem t.impure cid
            || is_partial_redundancy t env l id cid then !!()
            else pure t env e >>| ignore)
end

(* Determine the placement of the instruction and then extract its rewritten
   contents. *)
let reify t env l =
  let* () = Hoisting.process_moved_nodes t env l in
  extract_label t l >>= function
  | Some e -> exp t env l e
  | None -> !!()

(* Rewrite a single instruction. *)
let step_insn t env i =
  let l = Insn.label i in
  env.cur <- l;
  reify t env l

(* Step through a single basic block and rewrite its contents accordingly. *)
let step t env l = match Resolver.resolve t.eg.input.reso l with
  | None when Label.is_pseudo l -> !!()
  | None | Some `insn _ ->
    Context.failf "%s: missing block %a" error_prefix Label.pp l ()
  | Some `blk b ->
    let* () = Blk.insns b |> Context.Seq.iter ~f:(step_insn t env) in
    env.cur <- l;
    reify t env l

(* Collect all of the rewritten instructions in a traversal of the
   dominator tree, starting at label `l`. *)
let collect t l =
  let env = init () in
  let q = Stack.singleton (l, env.scp) in
  let rec loop () = match Stack.pop q with
    | None -> !!env
    | Some (l, scp) ->
      env.scp <- scp;
      let* () = step t env l in
      Tree.children t.eg.input.dom l |>
      Seq.iter ~f:(fun l -> Stack.push q (l, env.scp));
      loop () in
  loop ()

(* Find the rewritten instruction at label `l`. *)
let find_insn env l =
  Hashtbl.find env.insn l |> Option.map ~f:(Insn.create ~label:l)

(* Find any new instructions to be prepended directly before label `l`.
   Note that the ordering is, by default, from oldest to newest ID, but
   this can be reversed for an efficient `rev_append` as seen below. *)
let find_news ?(rev = false) env l =
  let order = if rev then `Decreasing_key else `Increasing_key in
  let seq = Id.Tree.to_sequence ~order in
  Hashtbl.find env.news l |>
  Option.value_map ~default:[] ~f:(fun m ->
      seq m |> Seq.map ~f:snd |>
      Seq.filter_map ~f:(find_insn env) |>
      Seq.to_list)

let move_dict i i' = Insn.(with_dict i' @@ dict i)

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
            let i =
              find_insn env label |>
              Option.value_map ~default:i ~f:(move_dict i) in
            let news = find_news env label ~rev:true in
            List.rev_append news (i :: acc)) in
      Blk.create () ~insns ~ctrl ~label
        ~args:(Blk.args b |> Seq.to_list)
        ~dict:(Blk.dict b))
