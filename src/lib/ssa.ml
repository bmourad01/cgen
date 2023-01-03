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

let find_blk fn l = match Fn.find_blk fn l with
  | Some _ as b -> b
  | None when Label.is_pseudo l -> None
  | None -> raise @@ Missing_blk (Fn.name fn, l)

let succs cfg fn l = Cfg.Node.succs l cfg |> Seq.filter_map ~f:(find_blk fn)

let collect_vars fn =
  Fn.blks fn |> Seq.map ~f:Blk.free_vars |>
  Seq.fold ~init:Var.Set.empty ~f:Set.union

let blocks_that_define_var x fn =
  Fn.blks fn |> Seq.filter ~f:(fun b -> Blk.defines_var b x) |>
  Seq.map ~f:Blk.label |> Seq.to_list_rev

let new_name vars nums x =
  Hashtbl.update nums x ~f:(function
      | Some x -> x + 1
      | None -> 1);
  let n = Hashtbl.find_exn nums x in
  let y = Var.with_index x n in
  Hashtbl.add_multi vars ~key:x ~data:y;
  y

let rename_phi vars nums b = Blk.map_phi b ~f:(fun _ p ->
    Insn.Phi.with_lhs p @@ new_name vars nums @@ Insn.Phi.lhs p)

let map_var vars x = match Hashtbl.find vars x with
  | None | Some [] -> x
  | Some (y :: _) -> y

let map_arg vars : Insn.arg -> Insn.arg = function
  | `var x -> `var (map_var vars x)
  | a -> a

let map_op vars (op : Insn.Data.op) =
  let arg = map_arg vars and var = map_var vars in match op with
  | `add (t, l, r) -> `add (t, arg l, arg r)
  | `div (t, l, r) -> `div (t, arg l, arg r)
  | `mul (t, l, r) -> `mul (t, arg l, arg r)
  | `neg (t, a) -> `neg (t, arg a)
  | `rem (t, l, r) -> `rem (t, arg l, arg r)
  | `sub (t, l, r) -> `sub (t, arg l, arg r)
  | `udiv (t, l, r) -> `udiv (t, arg l, arg r)
  | `urem (t, l, r) -> `urem (t, arg l, arg r)
  | `and_ (t, l, r) -> `and_ (t, arg l, arg r)
  | `or_ (t, l, r) -> `or_ (t, arg l, arg r)
  | `sar (t, l, r) -> `sar (t, arg l, arg r)
  | `shl (t, l, r) -> `shl (t, arg l, arg r)
  | `shr (t, l, r) -> `shr (t, arg l, arg r)
  | `xor (t, l, r) -> `xor (t, arg l, arg r)
  | `alloc _ -> op
  | `load (t, m, a) -> `load (t, var m, arg a)
  | `store (t, m, a, v) -> `store (t, var m, arg a, arg v)
  | `eq (t, l, r) -> `eq (t, arg l, arg r)
  | `ge (t, l, r) -> `ge (t, arg l, arg r)
  | `gt (t, l, r) -> `gt (t, arg l, arg r)
  | `le (t, l, r) -> `le (t, arg l, arg r)
  | `lt (t, l, r) -> `lt (t, arg l, arg r)
  | `ne (t, l, r) -> `ne (t, arg l, arg r)
  | `o (t, l, r) -> `o (t, arg l, arg r)
  | `sge (t, l, r) -> `sge (t, arg l, arg r)
  | `sgt (t, l, r) -> `sgt (t, arg l, arg r)
  | `sle (t, l, r) -> `sle (t, arg l, arg r)
  | `slt (t, l, r) -> `slt (t, arg l, arg r)
  | `uo (t, l, r) -> `uo (t, arg l, arg r)
  | `bits (t, a) -> `bits (t, arg a)
  | `ftosi (t, i, f) -> `ftosi (t, i, arg f)
  | `ftoui (t, i, f) -> `ftoui (t, i, arg f)
  | `ftrunc (t, f) -> `ftrunc (t, arg f)
  | `itrunc (t, i) -> `itrunc (t, arg i)
  | `sext (t, i) -> `sext (t, arg i)
  | `sitof (t, f, i) -> `sitof (t, f, arg i)
  | `uitof (t, f, i) -> `uitof (t, f, arg i)
  | `zext (t, i) -> `zext (t, arg i)
  | `copy (t, a) -> `copy (t, arg a)
  | `select (t, c, l, r) -> `select (t, var c, arg l, arg r)

let map_global vars : Insn.global -> Insn.global = function
  | `var x -> `var (map_var vars x)
  | g -> g

let map_dst vars : Insn.dst -> Insn.dst = function
  | #Insn.global as g -> (map_global vars g :> Insn.dst)
  | d -> d

let rename_data vars nums b =
  let glo = map_global vars in
  let margs = List.map ~f:(map_arg vars) in
  Blk.map_data b ~f:(fun _ -> function
      | `acall (x, t, f, args) ->
        `acall (new_name vars nums x, t, glo f, margs args)
      | `acallv (x, t, f, args) ->
        `acallv (new_name vars nums x, t, glo f, margs args)
      | `call (f, args) -> `call (glo f, margs args)
      | `callv (f, args) -> `callv (glo f, margs args)
      | `op (x, o) -> `op (new_name vars nums x, map_op vars o))

let rename_ctrl vars b =
  let var = map_var vars in
  let dst = map_dst vars in
  let arg = map_arg vars in
  Blk.map_ctrl b ~f:(fun _ -> function
      | `jmp d -> `jmp (dst d)
      | `jnz (c, t, f) -> `jnz (var c, dst t, dst f)
      | `ret None as r -> r
      | `ret (Some a) -> `ret (Some (arg a))
      | `switch (t, i, d, tbl) -> `switch (t, var i, d, tbl))

let update_phi vars l b =
  let var = map_var vars in
  Blk.map_phi b ~f:(fun _ p ->
      Insn.Phi.ins p |> Seq.fold ~init:p ~f:(fun p -> function
          | l', `var x when Label.(l' = l) ->
            Insn.Phi.update p l @@ `var (var x)
          | _ -> p))

let update_blk fn b =
  let l = Blk.label b in
  Fn.map_blks fn ~f:(fun b' ->
      if Label.equal l @@ Blk.label b' then b else b')

let pop_phi b pop =
  Blk.phi b |>
  Seq.map ~f:Insn.insn |>
  Seq.map ~f:Insn.Phi.lhs |>
  Seq.iter ~f:pop

let pop_data b pop =
  Blk.data b |>
  Seq.map ~f:Insn.insn |>
  Seq.filter_map ~f:Insn.Data.lhs |>
  Seq.iter ~f:pop

let pop_defs vars b =
  let pop x = Var.base x |> Hashtbl.change vars ~f:(function
      | Some (_ :: xs) -> Some xs
      | xs -> xs) in
  pop_phi b pop;
  pop_data b pop

let rec rename_block vars nums cfg dom fn' l =
  let fn = find_blk fn' l |> Option.value_map ~default:fn' ~f:(fun b ->
      rename_phi vars nums b |>
      rename_data vars nums |>
      rename_ctrl vars |>
      update_blk fn') in
  let fn = succs cfg fn l |> Seq.fold ~init:fn ~f:(fun fn b ->
      update_blk fn @@ update_phi vars l b) in
  let fn =
    Cfg.nodes cfg |>
    Seq.filter ~f:(Tree.is_child_of ~parent:l dom) |>
    Seq.fold ~init:fn ~f:(rename_block vars nums cfg dom) in
  Option.iter (find_blk fn' l) ~f:(pop_defs vars);
  fn

let has_phi_for_var b x =
  Blk.phi b |> Seq.exists ~f:(fun p -> Var.(x = Insn.lhs_of_phi p))

let insert_phi_node ins b lhs typ =
  if not @@ has_phi_for_var b lhs then
    let ins =
      Seq.map ins ~f:(fun b -> Blk.label b, `var lhs) |>
      Seq.to_list_rev in
    Insn.Phi.create ~lhs ~ins ~typ () >>?
    Context.Virtual.phi >>|
    Blk.insert_phi b
  else !!b

let insert_phi_nodes vars fn frontier cfg =
  Set.to_sequence vars |> Context.Seq.fold ~init:fn ~f:(fun fn x ->
      let bs = blocks_that_define_var x fn in
      iterated_frontier frontier (Label.pseudoentry :: bs) |>
      Set.to_sequence |> Context.Seq.fold ~init:fn ~f:(fun fn l ->
          match find_blk fn l with
          | None -> !!fn
          | Some b ->
            let ins =
              Cfg.Node.preds l cfg |>
              Seq.filter_map ~f:(find_blk fn) in
            (* XXX: FIXME *)
            insert_phi_node ins b x `i64 >>| update_blk fn))

let rename cfg dom fn =
  let vars = Var.Table.create () in
  let nums = Var.Table.create () in
  rename_block vars nums cfg dom fn Label.pseudoentry

let run fn = try
    let cfg = Cfg.create fn in
    let vars = collect_vars fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    let frontier = Graphlib.dom_frontier (module Cfg) cfg dom in
    insert_phi_nodes vars fn frontier cfg >>| rename cfg dom
  with Missing_blk (fn, l) ->
    Context.fail @@ Error.createf
      "SSA: missing block %a in function %s"
      Label.pps l fn
