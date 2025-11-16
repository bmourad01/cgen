open Core
open Monads.Std
open Egraph_common

module Subst = Egraph_subst
module Sched = Egraph_sched
module Uf = Egraph_uf
module O = Monad.Option

open O.Syntax

(* Canonicalize the node according to union-find. *)
let canon t : enode -> enode = function
  | N (_, []) as n -> n
  | N (op, cs) -> N (op, List.map cs ~f:(find t))
  | U _ -> assert false

(* See if the node is commutative, and if so, swap the arguments
   and check to see if we hash-consed it already.

   We can't add a rewrite rule for this because it would blow up
   the e-graph very quickly (since it trivially introduces an
   infinite loop).
*)
let commute t n = Enode.commute n >>= Hashtbl.find t.memo

let new_node ?ty t n =
  let id = Uf.fresh t.classes in
  Vec.push t.node n;
  Vec.push t.typs @@ Uopt.of_option ty;
  Vec.push t.ilbl Uopt.none;
  Vec.push t.imoved Lset.empty;
  assert (id = Vec.length t.node - 1);
  assert (id = Vec.length t.typs - 1);
  assert (id = Vec.length t.ilbl - 1);
  assert (id = Vec.length t.imoved - 1);
  id

(* Ensure that the term for `id` has type `ty`. *)
let check_union_type ?ty t id =
  Option.equal Type.equal ty @@ typeof t id

(* Represent the union of two e-classes with a "union" node. *)
let union ?ty t id oid =
  let u = new_node ?ty t @@ U {pre = id; post = oid} in
  Uf.union t.classes id oid;
  Uf.union t.classes id u;
  Sched.merge t id oid u;
  u

(* Called when a duplicate node is inserted. *)
let duplicate ?l t id =
  Option.iter l ~f:(Sched.duplicate t id);
  id

let subst_info t id : Subst.info = {
  const = const t id;
  typ = typeof t id;
  id;
}

let infer_ty t n = Enode.infer_ty n
    ~tid:(typeof t)
    ~tty:(typeof_typ t)
    ~tvar:(typeof_var t)
    ~word:(word t)

(* Rewrite state. *)
type rws = {
  mutable id     : id;  (* The newest ID. *)
  mutable budget : int; (* Remaining rewrites. *)
}

(* This is the entry point to the insert/rewrite loop, to
   be called from the algorithm in `Egraph_builder` (i.e.
   in depth-first dominator tree order). *)
let rec insert ?ty ?l ~d t n =
  canon t n |> Hashtbl.find_and_call t.memo
    ~if_found:(duplicate ?l t)
    ~if_not_found:(fun k -> match commute t k with
        | Some id -> duplicate ?l t id
        | None ->
          let ty = match ty with
            | None -> infer_ty t n
            | Some _ -> ty in
          let id = new_node ?ty t n in
          Option.iter l ~f:(fun l -> Sched.add t l id n);
          let oid = optimize ?ty ?l ~d t n id in
          Hashtbl.set t.memo ~key:k ~data:oid;
          oid)

and optimize ?ty ?l ~d t n id =
  match Enode.eval ~node:(node t) n with
  | Some c ->
    (* If the term normalizes to a constant then we don't need to
       waste time searching for matches. *)
    let k = Enode.of_const c in
    let oid = match Hashtbl.find t.memo k with
      | None ->
        let oid = new_node ?ty t k in
        Hashtbl.set t.memo ~key:k ~data:oid;
        oid
      | Some oid ->
        assert (check_union_type ?ty t oid);
        oid in
    Uf.union t.classes oid id;
    oid
  | None -> match n with
    | U _ -> assert false
    | N _ when d <= 0 -> id
    | N _ when Matcher.is_empty t.rules -> id
    | N _ ->
      let vm = VM.create () in
      let rws = {id; budget = t.match_limit} in
      if VM.init ~lookup:(node t) vm t.rules id then begin
        (* Cap the number of new terms that can be inserted. For large
           chains of union nodes this helps to keep the running time
           from exploding. *)
        let continue = ref true in
        while !continue && rws.budget > 0 do
          continue := match VM.one vm t.rules with
            | Some y -> rewrite ?ty ?l ~d:(d - 1) t rws y
            | None -> false
        done;
      end;
      rws.id

and rewrite ?ty ?l ~d t rws y =
  let exception Mismatch in
  (* Check that all variables on the RHS are in the substitution,
     so that we don't insert useless terms into the e-graph only
     to run into an uninstantiated variable. *)
  let rec check env : pattern -> unit = function
    | V x when Map.mem env x -> ()
    | V _ -> raise_notrace Mismatch
    | P (_, ps) -> List.iter ps ~f:(check env) in
  (* Assemble the RHS of the rule. *)
  let rec assemble env : pattern -> id = function
    | V x -> (Map.find_exn env x).Subst.id
    | P (o, ps) ->
      let cs = List.map ps ~f:(assemble env) in
      insert ?l ~d t @@ N (o, cs) in
  (* Not immediately obvious that this is an optimal term, so make
     a union node to record the equivalence. *)
  let default oid =
    rws.id <- union ?ty t rws.id oid;
    rws.budget <- rws.budget - 1 in
  (* We've transformed to a constant, or an otherwise optimal
     term, so we can end the search here. Note that we don't
     insert a union node in this case, but we still record the
     equivalence via union-find. All future rewrites w.r.t
     this e-class will refer only to this new term. *)
  let optimal oid =
    Uf.union t.classes rws.id oid;
    rws.id <- oid in
  try
    let env = Map.map (Y.subst y) ~f:(subst_info t) in
    let action, subsume = Y.payload y in
    let go env p = check env p; assemble env p in
    let oid = match action with
      | Static p -> go env p
      | Cond (p, k) when k env -> go env p
      | Cond _ -> raise_notrace Mismatch
      | Dyn f -> match f env with
        | Some p -> go env p
        | None -> raise_notrace Mismatch in
    (* No change. *)
    rws.id = oid ||
    (* Ill-typed. *)
    not (check_union_type ?ty t oid) ||
    (* Rewrite is OK, integrate with the current e-class. *)
    let continue = not (subsume || Enode.is_const (node t oid)) in
    if continue then default oid else optimal oid;
    continue
  with Mismatch -> true
