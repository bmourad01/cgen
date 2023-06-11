(* Adapted from: https://github.com/verse-lab/ego *)

open Core
open Virtual

module Id = Id
module Enode = Enode

type exp = E of Enode.op * exp list
[@@deriving compare, equal, sexp]

let rec pp_exp ppf = function
  | E (o, []) -> Format.fprintf ppf "%a" Enode.pp_op o
  | E (o, args) ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    Format.fprintf ppf "%a(%a)" Enode.pp_op o
      (Format.pp_print_list ~pp_sep pp_exp) args

module Exp = struct
  type t = exp [@@deriving compare, equal, sexp]

  let pp = pp_exp
  let op (E (op, _)) = op
  let args (E (_, args)) = args
  let exp op = E (op, [])
  let (&) op args = E (op, args)
end

type id = Id.t
[@@deriving compare, equal, hash, sexp]

type enode = Enode.t
[@@deriving compare, equal, hash, sexp]

type eclass = {
  id           : Id.t;
  nodes        : Enode.t Vec.t;
  parents      : (Enode.t * Id.t) Vec.t;
  mutable data : const option;
}

let create_eclass id = {
  id;
  nodes = Vec.create ();
  parents = Vec.create ();
  data = None;
}

type t = {
  uf        : Uf.t;
  nodes     : (enode, id) Hashtbl.t;
  classes   : eclass Id.Table.t;
  pending   : (enode * id) Vec.t;
  analyses  : (enode * id) Vec.t;
  mutable v : int;
}

let create () = {
  uf = Uf.create ();
  nodes = Hashtbl.create (module Enode);
  classes = Id.Table.create ();
  pending = Vec.create ();
  analyses = Vec.create ();
  v = 0;
}

type query =
  | V of string
  | Q of Enode.op * query list
[@@deriving compare, equal, sexp]

(* Substitute query variables with an e-class ID. *)
type subst = id String.Map.t

(* A callback for the rule. *)
type 'a callback = t -> id -> subst -> 'a

type formula =
  | Const of query
  | Cond of query * bool callback
  | Dyn of query option callback

type rule = {
  pre  : query;
  post : formula;
}

module Rule = struct
  type t = rule

  let var x = V x
  let exp o = Q (o, [])
  let (&) o q = Q (o, q)
  let (=>) pre post = {pre; post = Const post}
  let (=>?) pre post ~if_ = {pre; post = Cond (post, if_)}
  let (=>*) pre gen = {pre; post = Dyn gen}
end

let eclass t id = Hashtbl.find_or_add t.classes id
    ~default:(fun () -> create_eclass id)

let remove_eclass t id =
  Option.value_exn @@ Hashtbl.find_and_remove t.classes id

let data t id =
  Hashtbl.find t.classes id |>
  Option.bind ~f:(fun c -> c.data)

let merge_data l r = match l, r with
  | Some l, Some r ->
    assert (equal_const l r);
    Some l, (false, false)
  | Some l, None -> Some l, (false, true)
  | None, Some r -> Some r, (true, false)
  | _ -> None, (false, false)

let rec add_enode t n =
  let n = Enode.canonicalize n t.uf in
  Uf.find t.uf @@ match Hashtbl.find t.nodes n with
  | Some id -> id
  | None ->
    t.v <- t.v + 1;
    let id = Uf.fresh t.uf in
    let c = eclass t id in
    let x = n, id in
    Vec.push c.nodes n;
    Enode.children n |> List.iter ~f:(fun ch ->
        Vec.push (eclass t ch).parents x);
    Vec.push t.pending x;
    Hashtbl.set t.nodes ~key:n ~data:id;
    modify_analysis t id;
    id

and add t (E (o, args)) =
  add_enode t @@ N (o, List.map args ~f:(add t))

and merge t a b =
  let a = Uf.find t.uf a in
  let b = Uf.find t.uf b in
  if Id.(a <> b) then begin
    t.v <- t.v + 1;
    let ca = eclass t a in
    let cb = eclass t b in
    let a, b =
      if Vec.length ca.parents < Vec.length cb.parents
      then b, a else a, b in
    assert Id.(a = Uf.union t.uf a b);
    let cb = remove_eclass t b in
    let ca = eclass t a in
    assert Id.(a = ca.id);
    Vec.append t.pending cb.parents;
    let ua, ub =
      let d, r = merge_data ca.data cb.data in
      ca.data <- d;
      r in
    if ua then Vec.append t.analyses ca.parents;
    if ub then Vec.append t.analyses cb.parents;
    Vec.append ca.nodes cb.nodes;
    Vec.append ca.parents cb.parents;
    modify_analysis t a
  end

and modify_analysis t id =
  data t id |> Option.map ~f:Enode.of_const |>
  Option.iter ~f:(fun n -> merge t (add_enode t n) id)

let sort_and_dedup t ~compare = 
  Vec.sort t ~compare;
  let prev = ref None in
  Vec.filter_inplace t ~f:(fun x -> match !prev with
      | Some y when compare x y = 0 -> false
      | Some _ | None -> prev := Some x; true)

let rebuild_classes t = Hashtbl.iter t.classes ~f:(fun c ->
    Vec.map_inplace c.nodes ~f:(Fn.flip Enode.canonicalize t.uf);
    sort_and_dedup c.nodes ~compare:Enode.compare)

let rec update_nodes t = match Vec.pop t.pending with
  | None -> ()
  | Some (n, cid) ->
    let n' = Enode.canonicalize n t.uf in
    if Enode.compare n n' <> 0 then
      Hashtbl.remove t.nodes n;
    begin match Hashtbl.find t.nodes n with
      | None -> Hashtbl.set t.nodes ~key:n ~data:cid
      | Some id -> merge t id cid
    end;
    update_nodes t

let rec update_analyses t = match Vec.pop t.analyses with
  | None -> ()
  | Some (n, cid) ->
    let cid = Uf.find t.uf cid in
    let d = Enode.eval n ~data:(data t) in
    let c = eclass t cid in
    assert Id.(c.id = cid);
    let u, _ =
      let d, r = merge_data c.data d in
      c.data <- d;
      r in
    if u then begin
      Vec.append t.analyses c.parents;
      modify_analysis t cid
    end;
    update_analyses t

let process_unions t =
  while not @@ Vec.is_empty t.pending do
    update_nodes t;
    update_analyses t
  done

let rebuild t =
  process_unions t;
  rebuild_classes t

(* Maps e-class IDs to equivalent e-nodes. *)
type classes = enode Vec.t Id.Table.t

let eclasses t : classes =
  let r = Id.Table.create () in
  Hashtbl.iteri t.nodes ~f:(fun ~key:n ~data:id ->
      let id = Uf.find t.uf id in
      Vec.push (Hashtbl.find_or_add r id ~default:Vec.create) n);
  r

type cost = (id -> int) -> enode -> int
type extractor = id -> exp

let extract t ~(cost : cost) : extractor =
  let costs = Id.Table.create () in
  let id_cost id = Uf.find t.uf id |> Hashtbl.find_exn costs |> fst in
  let has_cost n = Enode.children n |> List.for_all ~f:(Hashtbl.mem costs) in
  let node_cost n = if has_cost n then Some (cost id_cost n) else None in
  let calculate ns =
    Vec.fold ns ~init:Int.Map.empty ~f:(fun m n ->
        node_cost n |> Option.value_map ~default:m
          ~f:(Map.update m ~f:(Option.value ~default:n))) |>
    Map.min_elt in
  let update ~key:id ~data:ns sat =
    let c = calculate ns in
    match Hashtbl.find costs id, c with
    | None, Some data ->
      Hashtbl.set costs ~key:id ~data;
      false
    | Some (x, _), Some ((y, _) as data) when compare y x < 0 ->
      Hashtbl.set costs ~key:id ~data;
      false
    | _ -> sat in
  let rec fixpoint (cs : classes) =
    Hashtbl.fold cs ~init:true ~f:update || fixpoint cs in
  let rec extract id =
    let id = Uf.find t.uf id in
    let _, n = Hashtbl.find_exn costs id in
    let cs = Enode.children n in
    E (Enode.op n, List.map cs ~f:extract) in
  ignore @@ fixpoint @@ eclasses t;
  extract

(* Map each e-class ID to a substitution environment. *)
type matches = subst Id.Map.t

let ematch t (cs : classes) p : matches =
  let rec enode env p (n : enode) = match p, n with
    | Q (x,  _), N (y,  _) when not @@ Enode.equal_op x y -> None
    | Q (_, xs), N (_, ys) -> args env xs ys
    | _ -> None
  and args env xs ys = match List.zip xs ys with
    | Ok l -> List.fold_until l ~finish:Fn.id ~init:(Some env) ~f:arg
    | Unequal_lengths -> None
  and arg acc (q, x) : _ Continue_or_stop.t = match acc with
    | None -> Stop None
    | Some env -> match go x q ~env with
      | Some _ as x -> Continue x
      | None -> Stop None
  and var env x id = match Map.find env x with
    | None -> Some (Map.set env ~key:x ~data:id)
    | Some id' -> Option.some_if Id.(id = id') env
  and first env q id =
    Option.(Hashtbl.find cs id >>= Vec.find_map ~f:(enode env q))
  and go ?(env = String.Map.empty) x =
    let id = Uf.find t.uf x in function
      | V x -> var env x id
      | Q _ as q -> first env q id in
  Hashtbl.fold cs ~init:Id.Map.empty ~f:(fun ~key:id ~data:_ m ->
      go id p |> Option.value_map ~default:m ~f:(fun env ->
          Map.set m ~key:id ~data:env))

let rec subst t (env : subst) = function
  | V x -> Map.find_exn env x
  | Q (o, q) -> add_enode t @@ N (o, List.map q ~f:(subst t env))

let apply t rules =
  let cs = eclasses t in
  List.iter rules ~f:(fun {pre; post} ->
      ematch t cs pre |> Map.iteri ~f:(fun ~key:id ~data:env ->
          let go q = merge t id @@ subst t env q in
          match post with
          | Const q -> go q
          | Cond (q, cond) -> if cond t id env then go q
          | Dyn gen -> gen t id env |> Option.iter ~f:go));
  rebuild t

let fixpoint ?fuel t rules = match fuel with
  | None ->
    let rec loop prev =
      apply t rules;
      t.v = prev || loop t.v in
    loop t.v
  | Some fuel ->
    let rec loop f prev =
      apply t rules;
      t.v = prev || (f > 0 && loop (f - 1) t.v) in
    loop fuel t.v
