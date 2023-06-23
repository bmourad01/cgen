(* Adapted from: https://github.com/verse-lab/ego *)

open Core
open Regular.Std
open Monads.Std
open Virtual

module Id = Id
module Enode = Enode
module O = Monad.Option

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
  uf          : Uf.t;
  nodes       : (enode, id) Hashtbl.t;
  classes     : eclass Id.Table.t;
  pending     : (enode * id) Vec.t;
  analyses    : (enode * id) Vec.t;
  mutable ver : int;
}

type egraph = t

let create () = {
  uf = Uf.create ();
  nodes = Hashtbl.create (module Enode);
  classes = Id.Table.create ();
  pending = Vec.create ();
  analyses = Vec.create ();
  ver = 0;
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

let find' t id = Uf.find t.uf id

let find_exn t (id : id) =
  let i = (id :> int) in
  if i < 0 || i >= Vec.length t.uf
  then invalid_argf "Invalid id %d" i ()
  else find' t id

let find t id = Option.try_with @@ fun () -> find_exn t id

let merge_data c l r ~left ~right = match l, r with
  | Some l, Some r -> assert (equal_const l r); c.data <- Some l
  | Some l, None   -> c.data <- Some l; right ()
  | None,   Some r -> c.data <- Some r; left ()
  | None,   None   -> c.data <- None
[@@specialise]

let rec add_enode t n =
  let n = Enode.canonicalize n t.uf in
  find' t @@ match Hashtbl.find t.nodes n with
  | Some id -> id
  | None ->
    t.ver <- t.ver + 1;
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
  let a = find' t a in
  let b = find' t b in
  if Id.(a <> b) then begin
    t.ver <- t.ver + 1;
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
    merge_data ca ca.data cb.data
      ~left:(fun () -> Vec.append t.analyses ca.parents)
      ~right:(fun () -> Vec.append t.analyses cb.parents);
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
[@@specialise]

let rebuild_classes t = Hashtbl.iter t.classes ~f:(fun c ->
    Vec.map_inplace c.nodes ~f:(Fn.flip Enode.canonicalize t.uf);
    sort_and_dedup c.nodes ~compare:Enode.compare)

let next v f = Option.iter ~f @@ Vec.pop v
[@@specialise]

let equal_children n n' =
  List.equal Id.equal (Enode.children n) (Enode.children n')

let update_node t n =
  let n' = Enode.canonicalize n t.uf in
  if not @@ equal_children n n' then Hashtbl.remove t.nodes n;
  n'

let rec update_nodes t = next t.pending @@ fun (n, cid) ->
  let n = update_node t n in
  Hashtbl.find_and_call t.nodes n
    ~if_not_found:(fun key -> Hashtbl.set t.nodes ~key ~data:cid)
    ~if_found:(fun id -> merge t id cid);
  update_nodes t

let rec update_analyses t = next t.analyses @@ fun (n, cid) ->
  let cid = find' t cid in
  let d = Enode.eval n ~data:(data t) in
  let c = eclass t cid in
  assert Id.(c.id = cid);
  merge_data c c.data d ~right:Fn.id ~left:(fun () ->
      Vec.append t.analyses c.parents;
      modify_analysis t cid);
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
      let id = find' t id in
      Vec.push (Hashtbl.find_or_add r id ~default:Vec.create) n);
  r

type cost = child:(id -> int) -> enode -> int

module Extractor = struct
  type t = {
    eg          : egraph;
    cost        : cost;
    table       : (int * enode) Id.Table.t;
    mutable ver : int;
    mutable sat : bool;
  }

  let init eg ~cost = {
    eg;
    cost;
    table = Id.Table.create ();
    ver = eg.ver;
    sat = false;
  }

  let id_cost t id = match Hashtbl.find t.table @@ find' t.eg id with
    | None -> failwithf "Couldn't calculate cost for node id %a" Id.pps id ()
    | Some (c, _) -> c

  let has_cost t n =
    Enode.children n |> List.for_all ~f:(Hashtbl.mem t.table)

  let node_cost t n =
    if not @@ has_cost t n then None
    else Some (t.cost ~child:(id_cost t) n, n)

  (* Find the least-expensive term. *)
  let best_term t ns =
    Vec.fold ns ~init:None ~f:(fun acc n ->
        node_cost t n |> Option.merge acc
          ~f:(fun ((c1, _) as a) ((c2, _) as b) ->
              if c2 < c1 then b else a))

  (* Saturate the cost table. *)
  let rec saturate t (cs : classes) =
    t.sat <- true;
    Hashtbl.iteri cs ~f:(fun ~key:id ~data:ns ->
        match Hashtbl.find t.table id, best_term t ns with
        | None, Some term ->
          Hashtbl.set t.table ~key:id ~data:term;
          t.sat <- false
        | Some (x, _), Some ((y, _) as term) when y < x ->
          Hashtbl.set t.table ~key:id ~data:term;
          t.sat <- false
        | _ -> ());
    if not t.sat then saturate t cs

  let rec extract_aux t id =
    let open O.Let in
    let id = find' t.eg id in
    let* _, n = Hashtbl.find t.table id in
    let+ cs = Enode.children n |> O.List.map ~f:(extract_aux t) in
    E (Enode.op n, cs)

  (* Check if the underlying e-graph has been updated. If so, we should
     re-compute the costs for each node. *)
  let check t = if t.ver <> t.eg.ver then begin
      Hashtbl.clear t.table;
      t.ver <- t.eg.ver;
      t.sat <- false;
    end

  let extract t id =
    check t;
    if not t.sat then saturate t @@ eclasses t.eg;
    extract_aux t id

  let extract_exn t id = match extract t id with
    | None -> invalid_argf "Couldn't extract term for id %a" Id.pps id ()
    | Some term -> term
end

type extractor = Extractor.t
type matches = (id * subst) Vec.t

(* Match a pre-condition with the available nodes in the graph. *)
let ematch t (cs : classes) p : matches =
  let rec enode env p (n : enode) = match p, n with
    | Q (x,  _), N (y,  _) when not @@ Enode.equal_op x y -> None
    | Q (_, xs), N (_, ys) -> args env xs ys
    | _ -> None
  and args init qs xs = match List.zip qs xs with
    | Ok l -> O.List.fold l ~init ~f:(fun env (q, x) -> go x q ~env)
    | Unequal_lengths -> None
  and var env x id = match Map.find env x with
    | None -> Some (Map.set env ~key:x ~data:id)
    | Some id' -> Option.some_if Id.(id = id') env
  and first env q id =
    O.(Hashtbl.find cs id >>= Vec.find_map ~f:(enode env q))
  and go ?(env = String.Map.empty) x =
    let id = find' t x in function
      | V x -> var env x id
      | Q _ as q -> first env q id in
  let r = Vec.create () in
  Hashtbl.iter_keys cs ~f:(fun id ->
      go id p |> Option.iter ~f:(fun env ->
          Vec.push r (id, env)));
  r

(* Apply the substitution environment to a post-condition. *)
let rec subst t (env : subst) = function
  | V x -> Map.find_exn env x
  | Q (o, q) -> add_enode t @@ N (o, List.map q ~f:(subst t env))

module Scheduler = struct
  type t = {
    match_limit : int;
    ban_length  : int;
  }

  let create_exn ?(match_limit = 1000) ?(ban_length = 5) () =
    if match_limit < 1 then invalid_arg "match_limit must be greater than zero";
    if ban_length < 1 then invalid_arg "ban_length must be greater than zero";
    {match_limit; ban_length}

  type data = {
    mutable banned_until : int;
    mutable times_banned : int;
  }

  let create_data () = {
    banned_until = 0;
    times_banned = 0;
  }

  let threshold t d = t.match_limit lsl d.times_banned

  let ban t d =
    (* XXX: a shift could set the MSB, which would give us a negative
       value, or it could overflow to zero. *)
    let b = t.ban_length lsl d.times_banned in
    d.banned_until <- if b <= 0 then Int.max_value else b;
    d.times_banned <- d.times_banned + 1

  (* This should be called when no changes are made after a single
     iteration, at which point we check if there are rules that we
     banned from being applied. If so, we should relax their ban
     lengths and try applying them again to see if we will get any
     changes. *)
  let should_stop t rules i =
    let banned = Seq.filter rules ~f:(fun (_, d) ->
        (* Reject rules that have been banned too many times. *)
        d.times_banned < Sys.int_size_in_bits &&
        (* Also reject rules that will never match. *)
        threshold t d > 0 &&
        d.banned_until > i) in
    Seq.min_elt banned ~compare:(fun (_, a) (_, b) ->
        compare a.banned_until b.banned_until) |>
    Option.value_map ~default:true ~f:(fun (_, d) ->
        let n = d.banned_until - i in
        Seq.iter banned ~f:(fun (_, d) ->
            d.banned_until <- d.banned_until - n);
        false)

  let check t d i =
    if d.times_banned < Sys.int_size_in_bits
    && i >= d.banned_until then
      (* XXX: can we assume that the result is zero if the shift
         overflows? *)
      let threshold = threshold t d in
      Option.some_if (threshold > 0) threshold
    else None

  let guard t d i ~(f : unit -> matches) : matches option =
    check t d i |> Option.bind ~f:(fun threshold ->
        let matches = f () in
        if Vec.length matches > threshold
        then (ban t d; None) else Some matches)
end

type scheduler = Scheduler.t

let fixpoint ?sched ?(fuel = Int.max_value) t rules =
  let sched = match sched with
    | None -> Scheduler.create_exn ()
    | Some sched -> sched in
  let rules = Seq.of_list @@ List.map rules ~f:(fun r ->
      r, Scheduler.create_data ()) in
  Seq.range 0 (max 1 fuel) |>
  Seq.fold_until ~init:t.ver ~finish:(const false) ~f:(fun prev i ->
      let cs = eclasses t in
      Seq.iter rules ~f:(fun (r, d) ->
          Scheduler.guard sched d i ~f:(fun () -> ematch t cs r.pre) |>
          Option.iter ~f:(Vec.iter ~f:(fun (id, env) ->
              let rewrite q = merge t id @@ subst t env q in
              match r.post with
              | Const q -> rewrite q
              | Cond (q, cond) -> if cond t id env then rewrite q
              | Dyn gen -> gen t id env |> Option.iter ~f:rewrite)));
      rebuild t;
      if t.ver = prev && Scheduler.should_stop sched rules i
      then Stop true else Continue t.ver)
