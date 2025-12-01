(* Reify to our CFG representation. *)

open Core
open Extractor_core
open Regular.Std
open Virtual

module Common = Egraph_common
module Lset = Label.Tree_set
module Iset = Egraph_id.Tree_set
module Id = Egraph_id

open Context.Syntax

(* Maps IDs to generated temporaries. We use a persistent map
   because it is scoped to the current line in the dominator
   tree. This way, we can duplicate code when we find a partial
   redundancy. *)
type scope = (Var.t * Label.t) Id.Tree.t

let empty_scope : scope = Id.Tree.empty

type placed = {
  seq : Label.t Ftree.t;
  ids : Bitset.t;
}

let create_placed id l = {
  seq = Ftree.singleton l;
  ids = Bitset.singleton id;
}

let add_placed p id l =
  assert (not @@ Bitset.mem p.ids id); {
    seq = Ftree.snoc p.seq l;
    ids = Bitset.set p.ids id;
  }

type env = {
  insn        : Insn.op Label.Table.t;
  ctrl        : ctrl Label.Table.t;
  news        : placed Label.Table.t;
  mutable cur : Label.t;
  mutable scp : scope;
}

let init () = {
  insn = Label.Table.create ();
  ctrl = Label.Table.create ();
  news = Label.Table.create();
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

let upd t x y = Hashtbl.update t x ~f:(Option.value ~default:y)

let fresh env canon real =
  match Id.Tree.find env.scp canon with
  | Some p -> !!p
  | None ->
    let* x = Context.Var.fresh in
    let+ l = Context.Label.fresh in
    env.scp <- Id.Tree.set env.scp ~key:canon ~data:(x, l);
    Logs.debug (fun m ->
        m "%s: placing fresh %a at %a: env.cur=%a canon=%d, real=%d%!"
          __FUNCTION__ Var.pp x Label.pp l Label.pp env.cur canon real);
    Hashtbl.update env.news env.cur ~f:(function
        | Some p -> add_placed p real l
        | None -> create_placed real l);
    x, l

let insn t env a f =
  let* x, l = match a with
    | Id {canon; real} -> fresh env canon real
    | Label l -> match Resolver.resolve t.eg.input.reso l with
      | Some `insn (_, _, Some x, _) -> !!(x, l)
      | Some _ | None -> no_var l in
  let+ op = f x in
  upd env.insn l op;
  `var x
[@@specialise]

let insn' env l f =
  let+ op = f () in
  upd env.insn l op
[@@specialise]

let ctrl env l f =
  let+ c = f () in
  upd env.ctrl l c
[@@specialise]

let sel e x ty c y n = match c with
  | `var c -> !!(`sel (x, ty, c, y, n))
  | `bool true -> !!(`uop (x, `copy ty, y))
  | `bool false -> !!(`uop (x, `copy ty, n))
  | _ -> invalid_pure e

let (let@) x f = x f [@@specialise] [@@inline]

let rec pure t env e : operand Context.t =
  let pure = pure t env in
  let insn = insn t env in
  match e with
  (* Only canonical forms are accepted. *)
  | E (a, Obinop b, [l; r]) ->
    let* l = pure l in
    let* r = pure r in
    let@ x = insn a in
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
    let@ x = insn a in
    sel e x ty c y n
  | E (_, Osingle s, []) -> !!(`float s)
  | E (_, Osym (s, n), []) -> !!(`sym (s, n))
  | E (a, Ounop u, [y]) ->
    let* y = pure y in
    let@ x = insn a in
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
    let@ () = ctrl in
    br l e c y n
  | E (_, Ocall0 _, [f; args; vargs]) ->
    let* f = global t env f in
    let* args = callargs t env args in
    let* vargs = callargs t env vargs in
    let@ () = insn in
    !!(`call (None, f, args, vargs))
  | E (_, Ocall (x, ty), [f; args; vargs]) ->
    let* f = global t env f in
    let* args = callargs t env args in
    let* vargs = callargs t env vargs in
    let@ () = insn in
    !!(`call (Some (x, ty), f, args, vargs))
  | E (_, Oload (x, t), [y]) ->
    let* y = pure y in
    let@ () = insn in
    !!(`load (x, t, y))
  | E (_, Ojmp, [d]) ->
    let* d = dst d in
    let@ () = ctrl in
    !!(`jmp d)
  | E (_, Oret, [x]) ->
    let* x = pure x in
    let@ () = ctrl in
    !!(`ret (Some x))
  | E (_, Oset _, [y]) -> pure y >>| ignore
  | E (_, Ostore (t, _), [v; x]) ->
    let* v = pure v in
    let* x = pure x in
    let@ () = insn in
    !!(`store (t, v, x))
  | E (_, Osw ty, i :: d :: tbl) ->
    let* i = pure i in
    let* d = sw_default t env l d in
    let* tbl = table t env tbl ty in
    let@ () = ctrl in
    sw l e ty i d tbl
  | E (_, Ovaarg (x, t), [a]) ->
    let* a = pure a in
    let@ () = insn in
    vaarg l e x t a
  | E (_, Ovastart _, [a]) ->
    let* a = pure a in
    let@ () = insn in
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
  (* Try the real ID first before moving on to the canonical ID. This could
     happen if we rescheduled a newer term before we unioned it with an older
     term. *)
  let find_moved t id cid =
    let s = Common.movedof t.eg id in
    if Lset.is_empty s then
      if id = cid then s else Common.movedof t.eg cid
    else s

  let resolve_label t l =
    match Resolver.resolve t.eg.input.reso l with
    | Some `insn (_, b, _, _) -> Blk.label b
    | Some `blk b -> Blk.label b
    | None -> assert false

  let moved_blks t id cid =
    find_moved t id cid |> Lset.map ~f:(resolve_label t)

  let rec post_dominated t l bs =
    match Semi_nca.Tree.parent t.eg.input.pdom l with
    | Some p -> Lset.mem bs p || post_dominated t p bs
    | None -> false

  (* See if there exists a cycle starting from `l` that does not intersect
     with `bs`. *)
  let exists_bypass t l id cid bs =
    let rec loop q = match Stack.pop q with
      | None -> false
      | Some (n, vis) when Lset.mem vis n ->
        (Label.(n = l) && Lset.disjoint vis bs) || loop q
      | Some (n, vis) ->
        let vis = Lset.add vis n in
        Cfg.Node.succs n t.eg.input.cfg |>
        Seq.iter ~f:(fun s -> Stack.push q (s, vis));
        loop q in
    let res =
      Loops.mem t.eg.input.loop l &&
      loop (Stack.singleton (l, Lset.empty)) in
    Logs.debug (fun m ->
        m "%s: %a is post-dominated: bs=%s, id=%d, cid=%d, res=%b%!"
          __FUNCTION__ Label.pp l
          (Lset.to_list bs |> List.to_string ~f:Label.to_string)
          id cid res);
    res

  (* Given all of the uses we know of, compute the points
     where the definition will be killed:

     kills = {k | ∃ u ∈ uses s.t. k ∈ succs(u) ∧ k ∉ uses}
  *)
  let compute_kills t uses =
    Lset.fold uses ~init:Lset.empty ~f:(fun init u ->
        Cfg.Node.succs u t.eg.input.cfg |>
        Seq.filter ~f:(Fn.non @@ Lset.mem uses) |>
        Seq.fold ~init ~f:Lset.add)

  (* See if there exists a path, starting from `l`, that avoids
     touching any block in `uses` and either reaches the end of
     the function, or one of the blocks in `kills`.

     `kills` is the set of blocks where, if we were to place the
     instruction at `l`, its live range would end.

     pre: `kills` and `uses` are disjoint
  *)
  let is_partial_redundancy_pathwise t l id cid ~uses =
    let kills = compute_kills t uses in
    let rec loop q = match Stack.pop q with
      | None -> false
      | Some (n, vis) when Lset.mem vis n -> loop q
      | Some (n, _) when Lset.mem uses n -> loop q
      | Some (n, _) when Lset.mem kills n -> true
      | Some (n, _) when Label.(n = pseudoexit) -> true
      | Some (n, vis) ->
        let vis = Lset.add vis n in
        Cfg.Node.succs n t.eg.input.cfg |>
        Seq.iter ~f:(fun s -> Stack.push q (s, vis));
        loop q in
    let res = loop @@ Stack.singleton (l, Lset.empty) in
    Logs.debug (fun m ->
        m "%s: l=%a, id=%d cid=%d, uses=%s, kills=%s, res=%b%!"
          __FUNCTION__ Label.pp l id cid
          (Lset.to_list uses |> List.to_string ~f:Label.to_string)
          (Lset.to_list kills |> List.to_string ~f:Label.to_string)
          res);
    res

  (* When we "move" duplicate nodes up to the LCA (lowest common ancestor)
     in the dominator tree, we might be introducing a partial redundancy.
     This means that, at the LCA, the node is not going to be used on all
     paths that are dominated by it, so we need to do a simple analysis to
     see if this is the case. *)
  let is_partial_redundancy t l id cid =
    (* If this node is deliberately placed here then allow it. *)
    not (Common.is_pinned t.eg id) && begin
      Logs.debug (fun m ->
          m "%s: checking %a, id=%d, cid=%d%!"
            __FUNCTION__ Label.pp l id cid);
      (* Get the blocks associated with the labels that were
         "moved" for this node. *)
      let bs = moved_blks t id cid in
      (* An empty set means that nobody uses this value. *)
      Lset.is_empty bs || begin
        (* If we're being used in the candidate block then this is trivially
           not a partial redundancy. *)
        let l = resolve_label t l in
        not (Lset.mem bs l) && begin
          (* If one of these blocks post-dominates the block that we're
             moving to, then it is safe to allow the move to happen,
             since we are inevitably going to compute it. However, this
             choice has a drawback in that it may extend the live range
             of this node beyond any benefit from hoisting it. In terms
             of native code generation, this means added register pressure,
             which may lead to increased spilling. *)
          if post_dominated t l bs then
            (* Check if we can reach the target block via a backedge
               without visiting any of the blocks we moved from. *)
            exists_bypass t l id cid bs
          else
            (* Check if `bs` intersects on all paths where `id` can
               be used. *)
            is_partial_redundancy_pathwise t l id cid ~uses:bs
        end
      end
    end

  let should_skip t l id cid =
    Bitset.mem t.impure cid ||
    is_partial_redundancy t l id cid

  (* If any nodes got moved up to this label, then we should check
     to see if it is eligible for this code motion optimization.

     Note that even if placing some nodes at this label would
     introduce a partial redundancy, there may still exist entries
     in the `lmoved` table that also map to these nodes, thus helping
     to minimize duplication as we traverse down the dominator tree.
  *)
  let process_moved_nodes t env l =
    match Hashtbl.find t.eg.lmoved l with
    | None -> !!()
    | Some s ->
      (* Explore the newest nodes first, ignoring those that have
         already been placed. *)
      Iset.to_sequence s ~order:`Decreasing |>
      Seq.map ~f:(fun id -> id, Common.find t.eg id) |>
      Seq.filter ~f:(fun (_, cid) -> not @@ Id.Tree.mem env.scp cid) |>
      Context.Seq.iter ~f:(fun (id, cid) -> match extract t id with
          | None -> extract_fail l id
          | Some e ->
            let@ () = Context.unless (should_skip t l id cid) in
            Logs.debug (fun m ->
                m "%s: id=%d, cid=%d was moved to l=%a, OK to hoist%!"
                  __FUNCTION__ id cid Label.pp l);
            pure t env e >>| ignore)
end

(* Determine placement of instructions at this label. *)
let reify t env l =
  let* () = Hoisting.process_moved_nodes t env l in
  match Hashtbl.find t.eg.lval l with
  | None -> !!()
  | Some id -> match extract t id with
    | None -> extract_fail l @@ Common.find t.eg id
    | Some (E (Id {canon; _}, op, args) as e)
      when not @@ Bitset.mem t.impure canon ->
      (* There may be an opportunity to "sink" this instruction,
         which is the dual of the "hoisting" optimization below.
         Since this is a pure operation, we can wait until it is
         actually needed by an effectful instruction or for
         control-flow. *)
      begin match op, args with
        | Oset _, [E (Id {canon; _}, _, _)]
          when Common.is_pinned t.eg canon ->
          Logs.debug (fun m ->
              m "%s: pinned: id=%d, l=%a%!"
                __FUNCTION__ id Label.pp l);
          exp t env l e
        | _ ->
          Logs.debug (fun m ->
              m "%s: delaying CFG extraction of id=%d, l=%a%!"
                __FUNCTION__ id Label.pp l);
          !!()
      end
    | Some e ->
      Logs.debug (fun m ->
          m "%s: eagerly extracting id=%d to l=%a in CFG%!"
            __FUNCTION__ id Label.pp l);
      exp t env l e

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
      Semi_nca.Tree.children t.eg.input.dom l |>
      Seq.iter ~f:(fun l -> Stack.push q (l, env.scp));
      loop () in
  loop ()

(* Find the rewritten instruction at label `l`. *)
let find_insn env l =
  Hashtbl.find env.insn l |> Option.map ~f:(Insn.create ~label:l)

(* Find any new instructions to be prepended directly before label `l`.
   The order can be reversed for an efficient `rev_append` as seen below. *)
let find_news ?(rev = false) env l =
  Hashtbl.find env.news l |>
  Option.value_map ~default:[] ~f:(fun p ->
      Ftree.enum ~rev p.seq |>
      Seq.filter_map ~f:(find_insn env) |>
      Seq.to_list)

let move_dict i i' = Insn.(with_dict i' @@ dict i)

let cfg t =
  let+ env = collect t Label.pseudoentry in
  Func.map_blks t.eg.input.fn ~f:(fun b ->
      let label = Blk.label b in
      let k = match Hashtbl.find env.ctrl label with
        | None -> Blk.ctrl b
        | Some c -> c in
      let is =
        Blk.insns b ~rev:true |>
        Seq.fold ~init:(find_news env label) ~f:(fun acc i ->
            let label = Insn.label i in
            let i =
              find_insn env label |>
              Option.value_map ~default:i ~f:(move_dict i) in
            let news = find_news env label ~rev:true in
            List.rev_append news (i :: acc)) in
      Blk.(with_ctrl (with_insns b is) k))
