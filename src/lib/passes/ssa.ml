open Core
open Graphlib.Std
open Regular.Std
open Virtual

exception Missing_blk of string * Label.t
exception Type_error of Error.t

type env = {
  fn       : func;
  cfg      : Cfg.t;
  fv       : Var.Set.t;
  dom      : Label.t tree;
  frontier : Label.t frontier;
  blks     : blk Label.Table.t;
  vars     : Var.t list Var.Table.t;
  nums     : int Var.Table.t;
  typs     : Typecheck.env;
}

let collect_vars fn =
  Func.blks fn |> Seq.map ~f:Blk.free_vars |>
  Seq.fold ~init:Var.Set.empty ~f:Set.union

let init fn typs =
  let cfg = Cfg.create fn in
  let fv = collect_vars fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  let frontier = Graphlib.dom_frontier (module Cfg) cfg dom in
  let blks = Label.Table.create () in
  let vars = Var.Table.create () in
  let nums = Var.Table.create () in
  Func.blks fn |> Seq.iter ~f:(fun blk ->
      Hashtbl.set blks ~key:(Blk.label blk) ~data:blk);
  {fn; cfg; fv; dom; frontier; blks; vars; nums; typs}

let find_blk env l = match Hashtbl.find env.blks l with
  | None when Label.is_pseudo l -> None
  | None -> raise @@ Missing_blk (Func.name env.fn, l)
  | Some _ as b -> b

let blocks_that_define_var env x =
  Hashtbl.fold env.blks
    ~init:Label.Set.empty
    ~f:(fun ~key:l ~data:b acc ->
        if Blk.defines_var b x
        then Set.add acc l
        else acc)

module Phi : sig
  val go : env -> unit
end = struct
  let args_of_vars = List.map ~f:(fun x -> `var x)

  let argify_local xs : local -> local = function
    | `label (l, args) as loc -> match Map.find xs l with
      | Some xs -> `label (l, args_of_vars xs @ args)
      | None -> loc

  let argify_dst xs : dst -> dst = function
    | #local as l -> (argify_local xs l :> dst)
    | d -> d

  let argify_ctrl xs b =
    let loc = argify_local xs in
    let dst = argify_dst xs in
    Blk.map_ctrl b ~f:(function
        | `hlt as h -> h
        | `jmp d -> `jmp (dst d)
        | `br (c, t, f) -> `br (c, dst t, dst f)
        | `ret _ as r -> r
        | `sw (t, i, d, tbl) ->
          let tbl = Ctrl.Table.map_exn tbl ~f:(fun v l -> v, loc l) in
          `sw (t, i, loc d, tbl))

  let update_ins env l x init =
    Cfg.Node.preds l env.cfg |>
    Seq.filter_map ~f:(find_blk env) |>
    Seq.fold ~init ~f:(fun ins b ->
        Blk.label b |> Map.update ins ~f:(function
            | None -> Label.Map.singleton l [x]
            | Some m -> Map.add_multi m ~key:l ~data:x))

  let typ_err env x c = Error.createf
      "Cannot have block argument for variable %a \
       of type :%s in function $%s" Var.pps x
      (Type.compound_name c) (Func.name env.fn)

  let blk_arg env x =
    match Typecheck.Env.typeof_var env.fn x env.typs with
    | Error err -> raise @@ Type_error err
    | Ok (#Type.compound as c) -> raise @@ Type_error (typ_err env x c)
    | Ok ((#Type.basic | #Type.special) as t) -> x, (t :> Blk.arg_typ)

  let update_blk_args env x ins l =
    find_blk env l |> Option.value_map ~default:ins ~f:(fun b ->
        let ins = update_ins env l x ins in
        let b = Blk.prepend_arg b @@ blk_arg env x in
        Hashtbl.set env.blks ~key:l ~data:b;
        ins)

  let iterated_frontier f blks =
    let blks = Set.add blks Label.pseudoentry in
    let df = Set.fold ~init:Label.Set.empty ~f:(fun init b ->
        Frontier.enum f b |> Seq.fold ~init ~f:Set.add) in
    let rec fixpoint idf =
      let idf' = df @@ Set.union idf blks in
      if Set.equal idf idf' then idf' else fixpoint idf' in
    fixpoint Label.Set.empty

  let insert_blk_args env =
    Set.fold env.fv ~init:Label.Map.empty ~f:(fun init x ->
        blocks_that_define_var env x |>
        iterated_frontier env.frontier |>
        Set.fold ~init ~f:(update_blk_args env x))

  let insert_ctrl_args env ins =
    Map.iteri ins ~f:(fun ~key ~data ->
        find_blk env key |> Option.iter ~f:(fun b ->
            Hashtbl.set env.blks ~key ~data:(argify_ctrl data b)))

  let go env = insert_blk_args env |> insert_ctrl_args env
end

module Rename : sig
  val go : env -> unit
end = struct
  let new_name env x =
    Hashtbl.update env.nums x ~f:(function
        | Some x -> x + 1
        | None -> 1);
    let n = Hashtbl.find_exn env.nums x in
    let y = Var.with_index x n in
    Hashtbl.add_multi env.vars ~key:x ~data:y;
    y

  let rename_args env b =
    Blk.map_args b ~f:(fun x t -> new_name env x, t)

  let map_var env x = match Hashtbl.find env.vars x with
    | None | Some [] -> x
    | Some (y :: _) -> y

  let map_arg env : operand -> operand = function
    | `var x -> `var (map_var env x)
    | a -> a

  let map_mem env (m : Insn.mem) =
    let arg = map_arg env in
    let rename = new_name env in
    match m with
    | `alloc (x, n) -> `alloc (rename x, n)
    | `load (x, t, a) -> `load (rename x, t, arg a)
    | `store (t, v, a) -> `store (t, arg v, arg a)

  let map_basic env (b : Insn.basic) =
    let arg = map_arg env in
    let var = map_var env in
    let rename = new_name env in
    match b with
    | `bop (x, b, l, r) -> `bop (rename x, b, arg l, arg r)
    | `uop (x, u, a) -> `uop (rename x, u, arg a)
    | `sel (x, t, c, l, r) -> `sel (rename x, t, var c, arg l, arg r)

  let map_global env : global -> global = function
    | `var x -> `var (map_var env x)
    | g -> g

  let map_local env : local -> local = function
    | `label (l, args) -> `label (l, List.map args ~f:(map_arg env))

  let map_dst vars : dst -> dst = function
    | #global as g -> (map_global vars g :> dst)
    | #local  as l -> (map_local  vars l :> dst)

  let rename_insns env b =
    let var = map_var env in
    let glo = map_global env in
    let margs = List.map ~f:(map_arg env) in
    let rename = new_name env in
    Blk.map_insns b ~f:(fun _ -> function
        | `call (Some (x, t), f, args, vargs) ->
          `call (Some (rename x, t), glo f, margs args, margs vargs)
        | `call (None, f, args, vargs) ->
          `call (None, glo f, margs args, margs vargs)
        | `vaarg (x, t, y) -> `vaarg (rename x, t, var y)
        | `vastart x -> `vastart (var x)
        | #Insn.basic as o -> map_basic env o
        | #Insn.mem as m -> map_mem env m)

  let rename_ctrl vars b =
    let var = map_var vars in
    let dst = map_dst vars in
    let loc = map_local vars in
    let arg = map_arg vars in
    Blk.map_ctrl b ~f:(function
        | `hlt as h -> h
        | `jmp d -> `jmp (dst d)
        | `br (c, t, f) -> `br (var c, dst t, dst f)
        | `ret None as r -> r
        | `ret (Some a) -> `ret (Some (arg a))
        | `sw (t, i, d, tbl) ->
          let tbl = Ctrl.Table.map_exn tbl ~f:(fun v l -> v, loc l) in
          `sw (t, var i, loc d, tbl))

  let pop_args b pop =
    Blk.args b |> Seq.map ~f:fst |> Seq.iter ~f:pop

  let pop_insns b pop =
    Blk.insns b |> Seq.filter_map ~f:Insn.lhs |> Seq.iter ~f:pop

  let pop_defs env b =
    let pop x = Var.base x |> Hashtbl.change env.vars ~f:(function
        | Some [] | None -> None
        | Some [x] -> None
        | Some (_ :: xs) -> Some xs) in
    pop_args b pop;
    pop_insns b pop

  let children env parent =
    Seq.filter ~f:(Tree.is_child_of env.dom ~parent) @@
    Cfg.nodes env.cfg

  let rec rename_block env l =
    let b = find_blk env l in
    Option.iter b ~f:(fun b ->
        rename_args env b |>
        rename_insns env |>
        rename_ctrl env |> fun b ->
        Hashtbl.set env.blks ~key:l ~data:b);
    children env l |> Seq.iter ~f:(rename_block env);
    Option.iter b ~f:(pop_defs env)

  let go env = rename_block env Label.pseudoentry
end

let try_ f = try f () with
  | Missing_blk (fn, l) ->
    Or_error.errorf
      "SSA: missing block %a in function %s"
      Label.pps l fn
  | Type_error err ->
    Or_error.errorf "SSA: type error: %s" @@
    Error.to_string_hum err

let run typs fn = try_ @@ fun () ->
  let env = init fn typs in
  Phi.go env;
  Rename.go env;
  Hashtbl.data env.blks |>
  Func.update_blks fn |>
  Or_error.return
