open Core
open Monads.Std
open Common

module O = Monad.Option
module I = Bv_interval

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

external float_of_bits : int64 -> float = "cgen_float_of_bits"
external float_to_bits : float -> int64 = "cgen_bits_of_float"

let single_val v ty : Virtual.const option = match ty with
  | #Type.imm as t -> Some (`int (v, t))
  | `f32 -> Some (`float (Float32.of_bits @@ Bv.to_int32 v))
  | `f64 -> Some (`double (float_of_bits @@ Bv.to_int64 v))
  | `flag -> Some (`bool Bv.(v <> zero))
  | _ -> None

let single_interval iv ty : Virtual.const option =
  let* iv = iv and* ty = ty in
  let* v = I.single_of iv in
  single_val v ty

let to_interval t : Virtual.const -> Bv_interval.t = function
  | `bool b -> I.boolean b
  | `int (value, t) ->
    I.create_single ~value ~size:(Type.sizeof_imm t)
  | `float f ->
    let value = Bv.M32.int32 @@ Float32.bits f in
    I.create_single ~value ~size:32
  | `double d ->
    let value = Bv.M64.int64 @@ float_to_bits d in
    I.create_single ~value ~size:64
  | `sym _ -> I.create_full ~size:(wordsz t)

(* If the node is already normalized then don't bother searching
   for matches. *)
let subsume_const ?iv ?ty t n id =
  match Enode.const ~node:(node t) n with
  | None ->
    let+ c, u = match Enode.eval ~node:(node t) n with
      | None ->
        let+ k = single_interval iv ty in
        k, false
      | Some k ->
        setiv ~iv:(to_interval t k) t id;
        Some (k, true) in
    let k = Enode.of_const c in
    let oid = Hashtbl.find_or_add t.memo k
        ~default:(fun () -> new_node t k) in
    if u then Uf.union t.classes id oid;
    oid
  | Some k ->
    setiv ~iv:(to_interval t k) t id;
    Some id

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

(* This is the entry point to the insert/rewrite loop, to be called
   from the algorithm in `Builder` (i.e. in depth-first dominator tree
   order).

   Note that we still continuously update the interval associated
   with the ID because it varies across program points.
*)
let rec insert ?iv ?ty ?l ~d ~rules t n =
  canon t n |> Hashtbl.find_and_call t.memo
    ~if_found:(fun id ->
        Option.iter l ~f:(Prov.duplicate t id);
        setiv ?iv t id;
        id)
    ~if_not_found:(fun k -> match commute t k with
        | Some id ->
          Option.iter l ~f:(Prov.duplicate t id);
          setiv ?iv t id;
          id
        | None ->
          let id = new_node t n in
          Option.iter l ~f:(fun l -> Prov.add t l id n);
          Option.iter ty ~f:(fun ty ->
              Hashtbl.set t.typs ~key:id ~data:ty);
          setiv ?iv t id;
          let oid = optimize ?iv ?ty ~d ~rules t n id in
          Hashtbl.set t.memo ~key:k ~data:oid;
          oid)

and optimize ?iv ?ty ~d ~rules t n id =
  match subsume_const ?iv ?ty t n id with
  | Some id -> id
  | None when d < 0 -> id
  | None ->
    search ?ty ~d:(d - 1) ~rules t n |>
    Vec.fold_until ~init:id ~finish:Fn.id ~f:(step t)

and search ?ty ~d ~rules t n =
  let m = Vec.create () in
  let u = Stack.create () in
  (* Match a node. *)
  let rec go (env : subst) p id (n : enode) = match p, n with
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
    | Some i -> Option.some_if (id = i.id) env
    | None ->
      let const = const t id in
      let intv = interval t id in
      let typ = typeof t id in
      Some (Map.set env ~key:x ~data:{const; intv; typ; id})
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
  | V x -> Map.find env x |> Option.map ~f:(fun i -> i.Subst.id)
  | P (o, ps) ->
    let+ cs = O.List.map ps ~f:(fun q ->
        apply_static ?ty ~d ~rules q t env) in
    insert ?ty ~d ~rules t @@ N (o, cs)

and apply_cond ?ty ~d ~rules q k t env =
  let* () = O.guard @@ k env in
  apply_static ?ty ~d ~rules q t env

and apply_dyn ?ty ~d ~rules q t env =
  let* q = q env in
  apply_static ?ty ~d ~rules q t env
