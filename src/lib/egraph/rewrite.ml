open Core
open Monads.Std
open Common

module O = Monad.Option

open O.Let
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

let new_node t n =
  let id = Uf.fresh t.classes in
  Vec.push t.node n;
  assert (id = Vec.length t.node - 1);
  id

(* If the node is already normalized then don't bother searching
   for matches. *)
let subsume_const t n id =
  let+ c = Enode.eval ~node:(node t) n in
  let k = Enode.of_const c in
  let oid = Hashtbl.find_or_add t.memo k
      ~default:(fun () -> new_node t k) in
  Uf.union t.classes id oid;
  oid

(* Represent the union of two e-classes with a "union" node. *)
let union t id oid =
  let u = new_node t @@ U {pre = id; post = oid} in
  Uf.union t.classes id oid;
  Uf.union t.classes id u;
  Prov.merge t id oid;
  Prov.merge t id u;
  u

(* Stop iterating when we find that we've optimized to a constant. *)
let step t id oid : (id, id) Continue_or_stop.t =
  if id <> oid then match node t oid with
    | n when Enode.is_const n ->
      Uf.union t.classes id oid;
      Stop oid
    | _ -> Continue (union t id oid)
  else Continue id

(* Called when a duplicate node is inserted. *)
let duplicate ?l t id =
  Option.iter l ~f:(Prov.duplicate t id);
  id

let subst_info t id : Subst.info = {
  const = const t id;
  typ = typeof t id;
  id;
}

let infer_ty t n = Enode.infer_ty n
    ~tid:(Hashtbl.find t.typs)
    ~tty:(typeof_typ t)
    ~tvar:(typeof_var t)
    ~word:(word t)

(* This is the entry point to the insert/rewrite loop, to be called
   from the algorithm in `Builder` (i.e. in depth-first dominator
   tree order). *)
let rec insert ?ty ?l ~d t n =
  canon t n |> Hashtbl.find_and_call t.memo
    ~if_found:(duplicate ?l t)
    ~if_not_found:(fun k -> match commute t k with
        | Some id -> duplicate ?l t id
        | None ->
          let id = new_node t n in
          let ty = match ty with
            | None -> infer_ty t n
            | Some _ -> ty in
          setty ?ty t id;
          Option.iter l ~f:(fun l -> Prov.add t l id n);
          let oid = optimize ~d t n id in
          Hashtbl.set t.memo ~key:k ~data:oid;
          oid)

and optimize ~d t n id = match subsume_const t n id with
  | Some id -> id
  | None when d < 0 -> id
  | None ->
    search ~d:(d - 1) t n |>
    Vec.fold_until ~init:id ~finish:Fn.id ~f:(step t)

and search ~d t n =
  let exception Mismatch in
  (* Pending unioned nodes. *)
  let pending = Stack.create () in
  (* IDs of rewritten terms. *)
  let matches = Vec.create ~capacity:t.match_limit () in
  (* Produce a substitution for an e-class. *)
  let rec cls env p id k = match p with
    | P (x, xs) -> pat env x xs id k
    | V x -> var env x id k
  (* Match a node with a concrete pattern. *)
  and pat env x xs id k = match node t id with
    | N (y, ys) when Enode.equal_op x y -> children ~env xs ys k
    | N _ -> raise_notrace Mismatch
    | U {pre; post} ->
      (* Bias towards the newer `post` term, but save the
         current continuation for the older `pre` term so
         we can try matching it later. *)
      Stack.push pending (env, x, xs, pre, k);
      pat env x xs post k
  (* Match all the children of an e-node. *)
  and children ?(env = empty_subst) ps cs k = match List.zip ps cs with
    | Unequal_lengths -> raise_notrace Mismatch
    | Ok l -> child env k l
  (* Match each child, providing a continuation for
     matching on the remaining children. *)
  and child env k = function
    | [] -> k env
    | [p, id] -> cls env p id k
    | (p, id) :: xs ->
      cls env p id @@ fun env ->
      child env k xs
  (* Produce a substitution for the variable. *)
  and var env x id k = k @@ Map.update env x ~f:(function
      | None -> subst_info t id
      | Some i when i.id = id -> i
      | Some _ -> raise_notrace Mismatch) in
  (* Insert a rewritten term based on the substitution. *)
  let rec rewrite env = function
    | P (o, ps) ->
      let cs = List.map ps ~f:(rewrite env) in
      insert ~d t @@ N (o, cs)
    | V x -> match Map.find env x with
      | None -> raise_notrace Mismatch
      | Some i -> i.Subst.id in
  (* Apply the action `a` to the substitution produced by `f`. *)
  let apply full a ~f =
    (* The running time can get seriously out of hand if we're
       matching over a large expression, so we cap the number
       of matches that will be considered. *)
    if Vec.length matches >= t.match_limit
    then full.return ()
    else try
        Vec.push matches @@ let env = f () in match a with
        | Static p -> rewrite env p
        | Cond (p, k) when k env -> rewrite env p
        | Cond _ -> raise_notrace Mismatch
        | Dyn f -> match f env with
          | Some p -> rewrite env p
          | None -> raise_notrace Mismatch
      with Mismatch -> () in
  (* Start by matching the top-level constructor. *)
  match n with
  | U _ -> assert false
  | N (o, cs) ->
    with_return (fun full ->
        Hashtbl.find t.rules o |>
        Option.iter ~f:(List.iter ~f:(fun (ps, a) ->
            (* Try matching with the children of the top-level node. *)
            apply full a ~f:(fun () -> children ps cs Fn.id);
            (* Now process any pending unioned nodes. *)
            Stack.until_empty pending @@ fun (env, x, xs, id, k) ->
            apply full a ~f:(fun () -> pat env x xs id k))));
    matches
