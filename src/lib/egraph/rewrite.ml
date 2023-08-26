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
  if not @@ Enode.is_const n then
    let+ c = Enode.eval ~node:(node t) n in
    let k = Enode.of_const c in
    let oid = Hashtbl.find_or_add t.memo k
        ~default:(fun () -> new_node t k) in
    Uf.union t.classes id oid;
    Prov.merge t id oid;
    oid
  else Some id

(* Represent the union of two e-classes with a "union" node. *)
let union t id oid =
  let u = new_node t @@ U {pre = id; post = oid} in
  Uf.union t.classes id oid;
  Uf.union t.classes id u;
  Prov.merge t id oid;
  Prov.merge t id u;
  u

(* Stop iterating when we find that we've optimized to a constant. *)
let step t id oid =
  let open Continue_or_stop in
  if id <> oid then match node t oid with
    | n when Enode.is_const n ->
      Uf.union t.classes id oid;
      Prov.merge t id oid;
      Stop oid
    | _ -> Continue (union t id oid)
  else Continue id

let rec insert ?ty ?l ~d ~rules t n =
  canon t n |> Hashtbl.find_and_call t.memo
    ~if_found:(fun id ->
        Option.iter l ~f:(Prov.duplicate t id);
        id)
    ~if_not_found:(fun k -> match commute t k with
        | Some id ->
          Option.iter l ~f:(Prov.duplicate t id);
          id
        | None ->
          let id = new_node t n in
          Option.iter l ~f:(fun l -> Prov.add t l id n);
          Option.iter ty ~f:(fun ty ->
              Hashtbl.set t.typs ~key:id ~data:ty);
          let oid = optimize ?ty ~d ~rules t n id in
          Hashtbl.set t.memo ~key:k ~data:oid;
          oid)

and optimize ?ty ~d ~rules t n id = match subsume_const t n id with
  | Some id -> id
  | None when d < 0 -> id
  | None ->
    search ?ty ~d:(d - 1) ~rules t n |>
    Vec.fold_until ~init:id ~finish:Fn.id ~f:(step t)

and search ?ty ~d ~rules t n =
  let m = Vec.create () in
  let u = Stack.create () in
  (* Match a node. *)
  let rec go env p id (n : enode) = match p, n with
    | V x, N _ -> var env x id
    | P (x, xs), N (y, ys) ->
      let* () = O.guard @@ Enode.equal_op x y in
      children env xs ys
    | _, U {pre; post} ->
      (* Explore the rewritten term first. In some cases, constant folding
         will run much faster if we keep rewriting it. If there's a match
         then we can enqueue the "original" term with the current state of
         the search for further exploration. *)
      match cls env post p with
      | Some _ as x -> Stack.push u (env, pre, p); x
      | None -> cls env pre p
  (* Match all the children of an e-node. *)
  and children init qs xs = match List.zip qs xs with
    | Ok l -> O.List.fold l ~init ~f:(fun env (q, x) -> cls env x q)
    | Unequal_lengths -> None
  (* Produce a substitution for the variable. *)
  and var env x id = match Map.find env x with
    | None -> Some (Map.set env ~key:x ~data:id)
    | Some id' -> Option.some_if (id = id') env
  (* Match an e-class. *)
  and cls env id = function
    | V x -> var env x id
    | P _ as q -> go env q id @@ node t id in
  (* Apply a post-condition to the substitution. *)
  let app f env =
    apply ?ty ~d ~rules f t env |>
    Option.iter ~f:(Vec.push m) in
  (* Now match based on the top-level constructor. *)
  match n with
  | U _ -> assert false
  | N (o, cs) ->
    Hashtbl.find rules o |>
    Option.iter ~f:(List.iter ~f:(fun (ps, f) ->
        children empty_subst ps cs |> Option.iter ~f:(app f);
        while not @@ Stack.is_empty u do
          let env, id, p = Stack.pop_exn u in
          cls env id p |> Option.iter ~f:(app f);
        done));
    m

and apply ?ty ~d ~rules = function
  | Static q -> apply_static ?ty ~d ~rules q
  | Cond (q, k) -> apply_cond ?ty ~d ~rules q k
  | Dyn q -> apply_dyn ?ty ~d ~rules q

and apply_static ?ty ~d ~rules q t env = match q with
  | V x -> Map.find env x
  | P (o, ps) ->
    let+ cs = O.List.map ps ~f:(fun q ->
        apply_static ?ty ~d ~rules q t env) in
    insert ?ty ~d ~rules t @@ N (o, cs)

and apply_cond ?ty ~d ~rules q k t env =
  let* () = O.guard @@ k t env in
  apply_static ?ty ~d ~rules q t env

and apply_dyn ?ty ~d ~rules q t env =
  let* q = q t env in
  apply_static ?ty ~d ~rules q t env
