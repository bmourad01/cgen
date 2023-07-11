open Core
open Regular.Std
open Common

(* Match a pre-condition with the available nodes in the graph. *)
let ematch t p : matches =
  let rec enode env p (n : enode) = match p, n with
    | Q (x,  _), N (y,  _) when not @@ Enode.equal_op x y -> None
    | Q (_, xs), N (_, ys) -> args env xs ys
    | _ -> None
  and args init qs xs = match List.zip qs xs with
    | Ok l -> O.List.fold l ~init ~f:(fun env (q, x) -> go x q ~env)
    | Unequal_lengths -> None
  and var env x id = match Map.find env x with
    | None -> Some (Map.set env ~key:x ~data:id)
    | Some id' -> Option.some_if (id = id') env
  and first env q id = Vec.find_map (eclass t id).nodes ~f:(enode env q)
  and go ?(env = String.Map.empty) x q =
    let id = find t x in match q with
    | V x -> var env x id
    | Q _ as q -> first env q id in
  let r = Vec.create () in
  Hashtbl.iter_keys t.classes ~f:(fun id ->
      go id p |> Option.iter ~f:(fun env ->
          Vec.push r (id, env)));
  r

(* Apply the substitution environment to a post-condition. *)
let rec subst t (env : subst) = function
  | V x -> Map.find_exn env x
  | Q (o, q) ->
    let q = List.map q ~f:(subst t env) in
    add_enode t @@ N (o, q)

let apply_const q t id env = merge t id @@ subst t env q
let apply_cond q k t id env = if k t id env then apply_const q t id env

let apply_dyn q t id env =
  q t id env |> Option.iter ~f:(fun q -> apply_const q t id env)

let apply = function
  | Const q -> apply_const q
  | Cond (q, k) -> apply_cond q k
  | Dyn q -> apply_dyn q

let apply t sched rules i =
  Seq.filter_map rules ~f:(fun d ->
      Scheduler.guard sched d i ~f:(fun () ->
          ematch t d.rule.pre) |>
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
