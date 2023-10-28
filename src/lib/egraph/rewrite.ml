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
let subsume_const ?iv ?ty t n id =
  let mkiv = Util.interval_of_const ~wordsz:(wordsz t) in
  match Enode.const ~node:(node t) n with
  | None ->
    let+ c, u = match Enode.eval ~node:(node t) n with
      | None ->
        let+ k = Util.single_interval iv ty in
        k, false
      | Some k ->
        setiv ~iv:(mkiv k) t id;
        Some (k, true) in
    let k = Enode.of_const c in
    let oid = Hashtbl.find_or_add t.memo k
        ~default:(fun () -> new_node t k) in
    (* Don't union with the constant if it came strictly from
       the intervals analysis. *)
    if u then Uf.union t.classes id oid;
    oid
  | Some k ->
    setiv ~iv:(mkiv k) t id;
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
let step t id oid : (id, id) Continue_or_stop.t =
  if id <> oid then match node t oid with
    | n when Enode.is_const n ->
      Uf.union t.classes id oid;
      Prov.merge t id oid;
      Stop oid
    | _ -> Continue (union t id oid)
  else Continue id

(* Called when a duplicate node is inserted. *)
let duplicate ?iv ?l t id =
  Option.iter l ~f:(Prov.duplicate t id);
  setiv ?iv t id;
  id

let subst_info t id : Subst.info = {
  const = const t id;
  intv = interval t id;
  typ = typeof t id;
  id;
}

let infer_ty_binop : Virtual.Insn.binop -> Type.t option = function
  | `add t
  | `div t
  | `mul t
  | `rem t
  | `sub t -> Some (t :> Type.t)
  | `mulh t
  | `udiv t
  | `umulh t
  | `urem t
  | `and_ t
  | `or_ t
  | `asr_ t
  | `lsl_ t
  | `lsr_ t
  | `rol t
  | `ror t
  | `xor t -> Some (t :> Type.t)
  | #Virtual.Insn.cmp -> Some `flag

let infer_ty_unop t : Virtual.Insn.unop -> Type.t option = function
  | `neg t
  | `copy t -> Some (t :> Type.t)
  | `clz t
  | `ctz t
  | `not_ t
  | `popcnt t
  | `flag t
  | `ftosi (_, t)
  | `ftoui (_, t)
  | `itrunc t
  | `sext t
  | `zext t -> Some (t :> Type.t)
  | `ifbits t | `ref t -> Some (t :> Type.t)
  | `fext t
  | `fibits t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) -> Some (t :> Type.t)
  | `unref n -> match Typecheck.Env.typeof_typ n t.input.tenv with
    | Ok t -> Some (t :> Type.t)
    | Error _ -> None

let infer_ty t : enode -> Type.t option = function
  | U {pre; post} ->
    let tpre = Hashtbl.find t.typs pre in
    let tpost = Hashtbl.find t.typs post in
    Option.merge tpre tpost ~f:(fun x y ->
        assert (Type.equal x y);
        x)
  | N (o, _) -> match o with
    | Oaddr _ -> Some (word t)
    | Obinop b -> infer_ty_binop b
    | Obool _ -> Some `flag
    | Obr -> None
    | Ocall0 _ -> None
    | Ocall (_, t) -> Some (t :> Type.t)
    | Ocallargs -> None
    | Odouble _ -> Some `f64
    | Ojmp -> None
    | Oint (_, t) -> Some (t :> Type.t)
    | Oload (_, t) -> Some (t :> Type.t)
    | Olocal _ -> None
    | Oret -> None
    | Osel t -> Some (t :> Type.t)
    | Oset _ -> None
    | Osingle _ -> Some `f32
    | Ostore _ -> None
    | Osw _ -> None
    | Osym _ -> Some (word t)
    | Otbl _ -> None
    | Otcall0 -> None
    | Otcall _ -> None
    | Ounop u -> infer_ty_unop t u
    | Ovaarg (_, t) -> Some (t :> Type.t)
    | Ovar x -> typeof_var t x
    | Ovastart _ -> None

exception Mismatch

(* This is the entry point to the insert/rewrite loop, to be called
   from the algorithm in `Builder` (i.e. in depth-first dominator tree
   order).

   Note that we still continuously update the interval associated
   with the ID because it varies across program points.
*)
let rec insert ?iv ?ty ?l ~d t n =
  canon t n |> Hashtbl.find_and_call t.memo
    ~if_found:(duplicate ?iv ?l t)
    ~if_not_found:(fun k -> match commute t k with
        | Some id -> duplicate ?iv ?l t id
        | None ->
          let id = new_node t n in
          let ty = match ty with
            | None -> infer_ty t n
            | Some _ -> ty in
          setty ?ty t id;
          setiv ?iv t id;
          Option.iter l ~f:(fun l -> Prov.add t l id n);
          let oid = optimize ?iv ?ty ~d t n id in
          Hashtbl.set t.memo ~key:k ~data:oid;
          oid)

and optimize ?iv ?ty ~d t n id =
  match subsume_const ?iv ?ty t n id with
  | Some id -> id
  | None when d < 0 -> id
  | None ->
    search ~d:(d - 1) t n |>
    Vec.fold_until ~init:id ~finish:Fn.id ~f:(step t)

and search ~d t n =
  let m = Vec.create () in
  let u = Stack.create () in
  (* Match a node. *)
  let rec go env p id n = match p, (n : enode) with
    | V x, N _ -> var env x id
    | P (x, xs), N (y, ys) when Enode.equal_op x y ->
      children ~init:env xs ys
    | P _, N _ -> raise Mismatch
    | _, U {pre; post} ->
      (* Explore the rewritten term first. In some cases, constant folding
         will run much faster if we keep rewriting it. If there's a match
         then we can enqueue the "original" term with the current state of
         the search for further exploration. *)
      try
        let env' = cls env post p in
        Stack.push u (env, pre, p);
        env'
      with Mismatch -> cls env pre p
  (* Match all the children of an e-node. *)
  and children ?(init = empty_subst) ps cs = match List.zip ps cs with
    | Ok l -> List.fold l ~init ~f:(fun env (p, c) -> cls env c p)
    | Unequal_lengths -> raise Mismatch
  (* Produce a substitution for the variable. *)
  and var env x id = match Map.find env x with
    | None -> Map.set env ~key:x ~data:(subst_info t id)
    | Some i when i.id = id -> env
    | Some _ -> raise Mismatch
  (* Match the canonical element of an e-class. *)
  and cls env id = function
    | P _ as p -> go env p id @@ node t id
    | V x -> var env x id in
  (* Insert a rewritten term based on the substitution. *)
  let rec rewrite ~d env = function
    | P (o, ps) ->
      let cs = List.map ps ~f:(rewrite ~d env) in
      insert ~d t @@ N (o, cs)
    | V x -> match Map.find env x with
      | None -> raise Mismatch
      | Some i -> i.Subst.id in
  (* Apply a post-condition to the substitution. *)
  let apply f env = Vec.push m @@ match f with
    | Static p -> rewrite ~d env p
    | Cond (p, k) when k env -> rewrite ~d env p
    | Cond _ -> raise Mismatch
    | Dyn f -> match f env with
      | Some p -> rewrite ~d env p
      | None -> raise Mismatch in
  let run f g = try apply f @@ g () with
    | Mismatch -> () in
  (* Now match based on the top-level constructor. *)
  match n with
  | U _ -> assert false
  | N (o, cs) ->
    Hashtbl.find t.rules o |>
    Option.iter ~f:(List.iter ~f:(fun (ps, f) ->
        (* Match the children of this node first. *)
        run f (fun () -> children ps cs);
        (* Then match any pending unioned nodes. *)
        while not @@ Stack.is_empty u do
          let env, id, p = Stack.pop_exn u in
          run f (fun () -> cls env id p)
        done));
    m
