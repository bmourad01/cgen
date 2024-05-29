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
  assert (id = Vec.length t.node - 1);
  assert (id = Vec.length t.typs - 1);
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

(* Raised when a rewrite rule is not applicable. This is intended
   to be caught locally during the search/rewrite phase. *)
exception Mismatch

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
          let oid = optimize ?ty ~d t n id in
          Hashtbl.set t.memo ~key:k ~data:oid;
          oid)

and optimize ?ty ~d t n id = match Enode.eval ~node:(node t) n with
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
    | N (o, cs) -> with_return @@ fun {return} ->
      (* The updated ID of the term. *)
      let rid = ref id in
      (* Pending unioned nodes. *)
      let pending = Stack.create () in
      (* The e-matching routine. *)
      let children, pat = search t pending in
      (* Inserts a rewritten term based on a substitution. *)
      let apply = rewrite ?ty ~d:(d - 1) t rid (ref t.match_limit) return in
      (* Start by matching the top-level constructor. *)
      Hashtbl.find t.rules o |> Option.iter ~f:(fun toplevels ->
          List.iter toplevels ~f:(fun (ps, a, subsume) ->
              (* Try matching with the children of the top-level node. *)
              apply a subsume ~f:(fun () -> children ps cs);
              (* Now process any pending unioned nodes. *)
              Stack.until_empty pending @@ fun (env, x, xs, id, k) ->
              apply a subsume ~f:(fun () -> pat env x xs id k)));
      !rid

and search t pending =
  (* Produce a substitution for an e-class. *)
  let rec cls env p id k = match p with
    | P (x, xs) -> pat env x xs id k
    | V x -> k @@ Map.update env x ~f:(function
        | None -> subst_info t id
        | Some i when i.id = id -> i
        | Some _ -> raise_notrace Mismatch)
  (* Match a node with a concrete pattern. *)
  and pat env x xs id k = match node t id with
    | N (y, ys) when Enode.equal_op x y -> children env xs ys k
    | N _ -> raise_notrace Mismatch
    | U {pre; post} ->
      (* Bias towards the newer `post` term, but save the
         current continuation for the older `pre` term so
         we can try matching it later. *)
      Stack.push pending (env, x, xs, pre, k);
      pat env x xs post k
  (* Match all the children of an e-node. *)
  and children env ps cs k = match List.zip ps cs with
    | Unequal_lengths -> raise_notrace Mismatch
    | Ok l -> child env k l
  (* Match each child, providing a continuation for
     matching on the remaining children. *)
  and child env k = function
    | [] -> k env
    | [p, id] -> cls env p id k
    | (p, id) :: xs ->
      cls env p id @@ fun env ->
      child env k xs in
  (* Return the entry points into the search. *)
  (fun ps cs -> children empty_subst ps cs Fn.id), pat

and rewrite ?ty ~d t id budget return action subsume ~f =
  (* Assemble the right-hand side of the rule. *)
  let rec go env = function
    | P (o, ps) ->
      let cs = List.map ps ~f:(go env) in
      insert ~d t @@ N (o, cs)
    | V x -> match Map.find env x with
      | None -> raise_notrace Mismatch
      | Some i -> i.Subst.id in
  (* Cap the number of new terms that can be inserted. For large
     chains of union nodes this helps to keep the running time
     from exploding. *)
  if !budget > 0 then try
      let env = f () in
      let oid = match action with
        | Static p -> go env p
        | Cond (p, k) when k env -> go env p
        | Cond _ -> raise_notrace Mismatch
        | Dyn f -> match f env with
          | Some p -> go env p
          | None -> raise_notrace Mismatch in
      if check_union_type ?ty t oid then match !id = oid with
        | false when subsume || Enode.is_const (node t oid) ->
          (* We've transformed to a constant, or an otherwise optimal
             term, so we can end the search here. Note that we don't
             insert a union node in this case, but we still record the
             equivalence via union-find. All future rewrites w.r.t
             this e-class will refer only to this new term. *)
          Uf.union t.classes !id oid;
          return oid
        | false ->
          decr budget;
          id := union ?ty t !id oid
        | true -> () 
    with Mismatch -> ()
  else return !id
