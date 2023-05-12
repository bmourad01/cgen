open Core
open Graphlib.Std
open Regular.Std
open Virtual

let iterated_frontier f blks =
  let df = Set.fold ~init:Label.Set.empty ~f:(fun init b ->
      Frontier.enum f b |> Seq.fold ~init ~f:Set.add) in
  let blks = List.fold blks ~init:Label.Set.empty ~f:Set.add in
  let rec fixpoint idf =
    let idf' = df @@ Set.union idf blks in
    if Set.equal idf idf' then idf' else fixpoint idf' in
  fixpoint Label.Set.empty

exception Missing_blk of string * Label.t

let find_blk fn l = match Func.find_blk fn l with
  | Some _ as b -> b
  | None when Label.is_pseudo l -> None
  | None -> raise @@ Missing_blk (Func.name fn, l)

let collect_vars fn =
  Func.blks fn |> Seq.map ~f:Blk.free_vars |>
  Seq.fold ~init:Var.Set.empty ~f:Set.union

let blocks_that_define_var x fn =
  Func.blks fn |> Seq.filter ~f:(fun b -> Blk.defines_var b x) |>
  Seq.map ~f:Blk.label |> Seq.to_list_rev

let new_name vars nums x =
  Hashtbl.update nums x ~f:(function
      | Some x -> x + 1
      | None -> 1);
  let n = Hashtbl.find_exn nums x in
  let y = Var.with_index x n in
  Hashtbl.add_multi vars ~key:x ~data:y;
  y

let rename_args vars nums b =
  Blk.map_args b ~f:(fun x t -> new_name vars nums x, t)

let map_var vars x = match Hashtbl.find vars x with
  | None | Some [] -> x
  | Some (y :: _) -> y

let map_arg vars : operand -> operand = function
  | `var x -> `var (map_var vars x)
  | a -> a

let map_mem vars nums (m : Insn.mem) =
  let arg = map_arg vars in
  let rename = new_name vars nums in
  match m with
  | `alloc (x, n) -> `alloc (rename x, n)
  | `load (x, t, a) -> `load (rename x, t, arg a)
  | `store (t, v, a) -> `store (t, arg v, arg a)

let map_basic vars nums (b : Insn.basic) =
  let arg = map_arg vars in
  let var = map_var vars in
  let rename = new_name vars nums in
  match b with
  | `bop (x, b, l, r) -> `bop (rename x, b, arg l, arg r)
  | `uop (x, u, a) -> `uop (rename x, u, arg a)
  | `sel (x, t, c, l, r) -> `sel (rename x, t, var c, arg l, arg r)

let map_global vars : global -> global = function
  | `var x -> `var (map_var vars x)
  | g -> g

let map_local vars : local -> local = function
  | `label (l, args) -> `label (l, List.map args ~f:(map_arg vars))

let map_dst vars : dst -> dst = function
  | #global as g -> (map_global vars g :> dst)
  | #local  as l -> (map_local  vars l :> dst)

let rename_insns vars nums b =
  let var = map_var vars in
  let glo = map_global vars in
  let margs = List.map ~f:(map_arg vars) in
  let rename = new_name vars nums in
  Blk.map_insns b ~f:(fun _ -> function
      | `call (Some (x, t), f, args, vargs) ->
        `call (Some (rename x, t), glo f, margs args, margs vargs)
      | `call (None, f, args, vargs) ->
        `call (None, glo f, margs args, margs vargs)
      | `vastart x -> `vastart (var x)
      | `vaarg (x, t, y) -> `vaarg (rename x, t, var y)
      | #Insn.basic as o -> map_basic vars nums o
      | #Insn.mem as m -> map_mem vars nums m)

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

let pop_defs vars b =
  let pop x = Var.base x |> Hashtbl.change vars ~f:(function
      | Some (_ :: xs) -> Some xs
      | xs -> xs) in
  pop_args b pop;
  pop_insns b pop

let rec rename_block vars nums cfg dom fn' l =
  let fn = match find_blk fn' l with
    | None -> fn'
    | Some b ->
      rename_args vars nums b |>
      rename_insns vars nums |>
      rename_ctrl vars |>
      Func.update_blk fn' in
  let fn =
    Cfg.nodes cfg |>
    Seq.filter ~f:(Tree.is_child_of ~parent:l dom) |>
    Seq.fold ~init:fn ~f:(rename_block vars nums cfg dom) in
  Option.iter (find_blk fn' l) ~f:(pop_defs vars);
  fn

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

exception Type_error of Error.t

let update_ins fn cfg l x init =
  Cfg.Node.preds l cfg |>
  Seq.filter_map ~f:(find_blk fn) |>
  Seq.fold ~init ~f:(fun ins b ->
      Blk.label b |> Map.update ins ~f:(function
          | None -> Label.Map.singleton l [x]
          | Some m -> Map.add_multi m ~key:l ~data:x))

let blk_arg env fn x = match Typecheck.Env.typeof_var fn x env with
  | Error err -> raise @@ Type_error err
  | Ok (#Type.compound as c) ->
    let err = Error.createf
        "Cannot have block argument for variable %a \
         of type :%s in function %s" Var.pps x
        (Type.compound_name c) (Func.name fn) in
    raise @@ Type_error err
  | Ok ((#Type.basic | #Type.special) as t) ->
    x, (t :> Blk.arg_typ)

let update_blk_args env fn cfg l x ins = match find_blk fn l with
  | None -> fn, ins
  | Some b ->
    let ins = update_ins fn cfg l x ins in
    let b = Blk.prepend_arg b @@ blk_arg env fn x in
    Func.update_blk fn b, ins

let insert_blk_args env vars fn frontier cfg =
  let init = fn, Label.Map.empty in
  Set.fold vars ~init ~f:(fun ((fn, _ins) as init) x ->
      let bs = blocks_that_define_var x fn in
      iterated_frontier frontier (Label.pseudoentry :: bs) |>
      Set.to_sequence |> Seq.fold ~init ~f:(fun (fn, ins) l ->
          update_blk_args env fn cfg l x ins))

let insert_ctrl_args fn ins =
  Map.fold ins ~init:fn ~f:(fun ~key ~data fn -> match find_blk fn key with
      | Some b -> Func.update_blk fn @@ argify_ctrl data b
      | None -> fn)

let insert_args env vars fn frontier cfg =
  let fn, ins = insert_blk_args env vars fn frontier cfg in
  insert_ctrl_args fn ins

let rename cfg dom fn =
  let vars = Var.Table.create () in
  let nums = Var.Table.create () in
  rename_block vars nums cfg dom fn Label.pseudoentry

let run env fn = try
    let cfg = Cfg.create fn in
    let vars = collect_vars fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    let frontier = Graphlib.dom_frontier (module Cfg) cfg dom in
    Ok (insert_args env vars fn frontier cfg |> rename cfg dom)
  with
  | Missing_blk (fn, l) ->
    Or_error.errorf
      "SSA: missing block %a in function %s"
      Label.pps l fn
  | Type_error err ->
    Or_error.errorf "SSA: type error: %s" @@
    Error.to_string_hum err
