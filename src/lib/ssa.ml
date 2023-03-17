open Core
open Virtual
open Graphlib.Std
open Regular.Std

open Context.Syntax

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

let succs cfg fn l = Cfg.Node.succs l cfg |> Seq.filter_map ~f:(find_blk fn)

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

let map_arg vars : Insn.arg -> Insn.arg = function
  | `var x -> `var (map_var vars x)
  | a -> a

let map_mem vars (m : Insn.Data.mem) =
  let arg = map_arg vars in
  let var = map_var vars in
  match m with
  | `alloc _ -> m
  | `load (t, m, a) -> `load (t, var m, arg a)
  | `store (t, m, a, v) -> `store (t, var m, arg a, arg v)

let map_basic vars nums (b : Insn.Data.basic) =
  let arg = map_arg vars in
  let var = map_var vars in
  let mem = map_mem vars in
  let rename = new_name vars nums in
  match b with
  | `bop (x, b, l, r) -> `bop (rename x, b, arg l, arg r)
  | `uop (x, u, a) -> `uop (rename x, u, arg a)
  | `mem (x, m) -> `mem (rename x, mem m)
  | `sel (x, t, c, l, r) -> `sel (rename x, t, var c, arg l, arg r)

let map_global vars : Insn.global -> Insn.global = function
  | `var x -> `var (map_var vars x)
  | g -> g

let map_local vars : Insn.local -> Insn.local = function
  | `label (l, args) -> `label (l, List.map args ~f:(map_arg vars))

let map_dst vars : Insn.dst -> Insn.dst = function
  | #Insn.global as g -> (map_global vars g :> Insn.dst)
  | #Insn.local  as l -> (map_local  vars l :> Insn.dst)

let rename_data vars nums b =
  let var = map_var vars in
  let glo = map_global vars in
  let margs = List.map ~f:(map_arg vars) in
  let rename = new_name vars nums in
  Blk.map_data b ~f:(fun _ -> function
      | `call (Some(x, t), f, args, vargs) ->
        `call (Some(rename x, t), glo f, margs args, margs vargs)
      | `call (None, f, args, vargs) ->
        `call (None, glo f, margs args, margs vargs)
      | `vastart x -> `vastart (var x)
      | #Insn.Data.basic as o -> map_basic vars nums o)

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
        let tbl = Insn.Ctrl.Table.map_exn tbl ~f:(fun v l -> v, loc l) in
        `sw (t, var i, loc d, tbl))

let pop_args b pop =
  Blk.args b |> Seq.map ~f:fst |> Seq.iter ~f:pop

let pop_data b pop =
  Blk.data b |> Seq.filter_map ~f:Insn.lhs_of_data |> Seq.iter ~f:pop

let pop_defs vars b =
  let pop x = Var.base x |> Hashtbl.change vars ~f:(function
      | Some (_ :: xs) -> Some xs
      | xs -> xs) in
  pop_args b pop;
  pop_data b pop

let rec rename_block vars nums cfg dom fn' l =
  let fn = match find_blk fn' l with
    | None -> fn'
    | Some b ->
      rename_args vars nums b |>
      rename_data vars nums |>
      rename_ctrl vars |>
      Func.update_blk fn' in
  let fn =
    Cfg.nodes cfg |>
    Seq.filter ~f:(Tree.is_child_of ~parent:l dom) |>
    Seq.fold ~init:fn ~f:(rename_block vars nums cfg dom) in
  Option.iter (find_blk fn' l) ~f:(pop_defs vars);
  fn

let has_arg_for_var b x =
  Blk.args b |> Seq.map ~f:fst |> Seq.exists ~f:(Var.equal x)

let args_of_vars = List.map ~f:(fun x -> `var x)

let argify_local xs : Insn.local -> Insn.local = function
  | `label (l, args) as loc -> match Map.find xs l with
    | Some xs -> `label (l, args_of_vars xs @ args)
    | None -> loc

let argify_dst xs : Insn.dst -> Insn.dst = function
  | #Insn.local as l -> (argify_local xs l :> Insn.dst)
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
        let tbl = Insn.Ctrl.Table.map_exn tbl ~f:(fun v l -> v, loc l) in
        `sw (t, i, loc d, tbl))

let insert_args vars fn frontier cfg =
  (* Insert arguments to basic blocks. *)
  let fn, ins = Set.fold vars ~init:(fn, Label.Map.empty) ~f:(fun (fn, ins) x ->
      let bs = blocks_that_define_var x fn in
      iterated_frontier frontier (Label.pseudoentry :: bs) |>
      Set.to_sequence |> Seq.fold ~init:(fn, ins) ~f:(fun (fn, ins) l ->
          match find_blk fn l with
          | None -> fn, ins
          | Some b ->
            let ins =
              Cfg.Node.preds l cfg |>
              Seq.filter_map ~f:(find_blk fn) |>
              Seq.fold ~init:ins ~f:(fun ins b ->
                  Blk.label b |> Map.update ins ~f:(function
                      | None -> Label.Map.singleton l [x]
                      | Some m -> Map.add_multi m ~key:l ~data:x)) in
            (* XXX: FIXME *)
            Blk.prepend_arg b (x, `i64) |> Func.update_blk fn, ins)) in
  (* Insert arguments to control instructions. *)
  Map.fold ins ~init:fn ~f:(fun ~key ~data fn -> match find_blk fn key with
      | Some b -> Func.update_blk fn @@ argify_ctrl data b
      | None -> fn)

let rename cfg dom fn =
  let vars = Var.Table.create () in
  let nums = Var.Table.create () in
  rename_block vars nums cfg dom fn Label.pseudoentry

let run fn = try
    let cfg = Cfg.create fn in
    let vars = collect_vars fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    let frontier = Graphlib.dom_frontier (module Cfg) cfg dom in
    Ok (insert_args vars fn frontier cfg |> rename cfg dom)
  with Missing_blk (fn, l) ->
    Or_error.errorf
      "SSA: missing block %a in function %s"
      Label.pps l fn
