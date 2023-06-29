open Core
open Regular.Std
open Common

(* Match a pre-condition with the available nodes in the graph. *)
let ematch t cs p : matches =
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
    let id = find t x in function
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
  | Q (o, q) -> add_enode t @@ N (o, substs t env q)

and substs t (env : subst) = List.map ~f:(subst t env)

let apply_const q t id env = merge t id @@ subst t env q
let apply_cond q k t id env = if k t id env then apply_const q t id env

let apply_dyn q t id env =
  q t id env |> Option.iter ~f:(fun q -> apply_const q t id env)

let apply = function
  | Const q -> apply_const q
  | Cond (q, k) -> apply_cond q k
  | Dyn q -> apply_dyn q

let next v f = Option.iter ~f @@ Vec.pop v [@@specialise]

let update_node t n =
  let n' = Enode.canonicalize n t.uf in
  if not @@ Enode.equal_children n n' then Hashtbl.remove t.nodes n;
  n'

let rec update_nodes t = next t.pending @@ fun (n, cid) ->
  let n = update_node t n in
  Hashtbl.find_and_call t.nodes n
    ~if_not_found:(fun key -> Hashtbl.set t.nodes ~key ~data:cid)
    ~if_found:(fun id -> merge t id cid);
  update_nodes t

let rec update_analyses t = next t.analyses @@ fun (n, cid) ->
  let cid = find t cid in
  let d = Enode.eval n ~data:(data t) in
  let c = eclass t cid in
  assert Id.(c.id = cid);
  merge_data c c.data d ~right:Fn.id ~left:(fun () ->
      Vec.append t.analyses c.parents;
      merge_analysis t cid);
  update_analyses t

let process_unions t = while not @@ Vec.is_empty t.pending do
    update_nodes t;
    update_analyses t
  done

let rebuild_classes t = Hashtbl.iter t.classes ~f:(fun c ->
    Vec.map_inplace c.nodes ~f:(Fn.flip Enode.canonicalize t.uf);
    sort_and_dedup c.nodes ~compare:Enode.compare)

let rebuild t =
  process_unions t;
  rebuild_classes t

let apply t sched rules i =
  let cs = eclasses t in
  Seq.filter_map rules ~f:(fun d ->
      Scheduler.guard sched d i ~f:(fun () ->
          ematch t cs d.rule.pre) |>
      Option.map ~f:(fun m ->
          apply d.Scheduler.rule.post, m)) |>
  Seq.iter ~f:(fun (apply, m) ->
      Vec.iter m ~f:(fun (id, env) -> apply t id env))

let step t sched rules i =
  let prev = t.ver in
  (* Apply the rules. *)
  apply t sched rules i;
  (* Restore canonical forms. *)
  rebuild t;
  (* If true, then fixpoint was reached. *)
  t.ver = prev && Scheduler.should_stop sched rules i

let fixpoint ?sched ?(fuel = Int.max_value) t rules =
  let sched = match sched with
    | None -> Scheduler.create_exn ()
    | Some sched -> sched in
  let rules = Scheduler.from_rules rules in
  fuel |> max 1 |> Seq.range 0 |> Seq.exists ~f:(step t sched rules)
