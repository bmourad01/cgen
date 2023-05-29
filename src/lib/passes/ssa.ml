open Core
open Graphlib.Std
open Regular.Std
open Virtual

exception Missing_blk of Label.t
exception Type_error of Error.t

type env = {
  fn       : func;
  cfg      : Cfg.t;
  fv       : Var.Set.t;
  dom      : Label.t tree;
  frontier : Label.t frontier;
  blks     : blk Label.Table.t;
  stk      : Var.t list Var.Table.t;
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
  let stk = Var.Table.create () in
  let nums = Var.Table.create () in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      Hashtbl.set blks ~key:(Blk.label b) ~data:b);
  {fn; cfg; fv; dom; frontier; blks; stk; nums; typs}

let typeof_var env x = Typecheck.Env.typeof_var env.fn x env.typs

let find_blk env l = match Hashtbl.find env.blks l with
  | None when Label.is_pseudo l -> None
  | None -> raise @@ Missing_blk l
  | Some _ as b -> b

(* First phase of the algorithm is to insert arguments to basic blocks
   and control-flow instructions based on the dominance frontier. *)
module Phi : sig
  val go : env -> unit
end = struct
  type state = {
    defs : Var.Set.t Label.Table.t;
    args : (Var.t * Blk.arg_typ) list Label.Table.t;
    ctrl : ctrl Label.Table.t;
    outs : Var.t list Label.Map.t Label.Table.t;
  }

  let define x = function
    | None -> Var.Set.singleton x
    | Some s -> Set.add s x

  let init env =
    let defs = Label.Table.create () in
    let args = Label.Table.create () in
    let ctrl = Label.Table.create () in
    let outs = Label.Table.create () in
    Hashtbl.iteri env.blks ~f:(fun ~key:l ~data:b ->
        let args' = Seq.to_list @@ Blk.args b in
        Hashtbl.set args ~key:l ~data:args';
        List.iter args' ~f:(fun (x, _) ->
            Hashtbl.update defs l ~f:(define x));
        Blk.insns b |> Seq.filter_map ~f:Insn.lhs |>
        Seq.iter ~f:(fun x -> Hashtbl.update defs l ~f:(define x));
        Hashtbl.set ctrl ~key:l ~data:(Blk.ctrl b));
    {defs; args; ctrl; outs}

  let blocks_that_define_var st x =
    Hashtbl.fold st.defs
      ~init:Label.Set.empty
      ~f:(fun ~key ~data s ->
          if Set.mem data x
          then Set.add s key
          else s)

  let update_incoming env l x outs =
    Cfg.Node.preds l env.cfg |> Seq.iter ~f:(fun l' ->
        Hashtbl.update outs l' ~f:(function
            | None -> Label.Map.singleton l [x]
            | Some inc -> Map.add_multi inc ~key:l ~data:x))

  let typ_err env x c = Error.createf
      "Cannot have block argument for variable %a \
       of type :%s in function $%s" Var.pps x
      (Type.compound_name c) (Func.name env.fn)

  let blk_arg env x = match typeof_var env x with
    | Error err -> raise @@ Type_error err
    | Ok (#Type.compound as c) -> raise @@ Type_error (typ_err env x c)
    | Ok ((#Type.basic | #Type.special) as t) -> x, (t :> Blk.arg_typ)

  let update_blk_args env st x l =
    update_incoming env l x st.outs;
    Hashtbl.add_multi st.args ~key:l ~data:(blk_arg env x);
    Hashtbl.update st.defs l ~f:(define x)

  let iterated_frontier f blks =
    let blks = Set.add blks Label.pseudoentry in
    let df = Set.fold ~init:Label.Set.empty ~f:(fun init b ->
        Frontier.enum f b |> Seq.fold ~init ~f:Set.add) in
    let rec fixpoint idf =
      let idf' = df @@ Set.union idf blks in
      if Set.equal idf idf' then idf' else fixpoint idf' in
    fixpoint Label.Set.empty

  let insert_blk_args env st =
    Set.iter env.fv ~f:(fun x ->
        blocks_that_define_var st x |>
        iterated_frontier env.frontier |>
        Set.iter ~f:(update_blk_args env st x))

  let args_of_vars = List.map ~f:(fun x -> `var x)

  let argify_local inc : local -> local = function
    | `label (l, args) as loc -> match Map.find inc l with
      | Some xs -> `label (l, args_of_vars xs @ args)
      | None -> loc

  let argify_dst inc : dst -> dst = function
    | #local as l -> (argify_local inc l :> dst)
    | d -> d

  let argify_tbl inc =
    Ctrl.Table.map_exn ~f:(fun v l -> v, argify_local inc l)

  let argify_ctrl inc c =
    let loc = argify_local inc in
    let dst = argify_dst inc in
    match c with
    | `hlt as h -> h
    | `jmp d -> `jmp (dst d)
    | `br (c, t, f) -> `br (c, dst t, dst f)
    | `ret _ as r -> r
    | `sw (t, i, d, tbl) -> `sw (t, i, loc d, argify_tbl inc tbl)

  let insert_ctrl_args env st =
    Hashtbl.iteri st.outs ~f:(fun ~key:l ~data:inc ->
        Hashtbl.update st.ctrl l ~f:(function
            | Some c -> argify_ctrl inc c
            | None -> assert false))

  let go env =
    let st = init env in
    insert_blk_args env st;
    insert_ctrl_args env st;
    Hashtbl.map_inplace env.blks ~f:(fun b ->
        let label = Blk.label b in
        let args = Hashtbl.find_exn st.args label in
        let ctrl = Hashtbl.find_exn st.ctrl label in
        let insns = Blk.insns b |> Seq.to_list in
        Blk.create ~args ~insns ~ctrl ~label ())
end

(* Second phase of the algorithm is to traverse the dominator tree
   and rename variables in each block according to their use-def
   chains. *)
module Rename : sig
  val go : env -> unit
end = struct
  let new_name env x =
    let default = 1 in
    let n = ref default in
    let upd x = n := x + 1; !n in
    Hashtbl.update env.nums x ~f:(Option.value_map ~default ~f:upd);
    let y = Var.with_index x !n in
    Hashtbl.add_multi env.stk ~key:x ~data:y;
    y

  let rename_args env b =
    Blk.args b |>
    Seq.map ~f:(fun (x, t) -> new_name env x, t) |>
    Seq.to_list

  let map_var env x = match Hashtbl.find env.stk x with
    | Some [] | None -> x
    | Some (y :: _) -> y

  let map_operand env : operand -> operand = function
    | `var x -> `var (map_var env x)
    | o -> o

  let map_global env : global -> global = function
    | `var x -> `var (map_var env x)
    | g -> g

  let map_local env : local -> local = function
    | `label (l, args) -> `label (l, List.map args ~f:(map_operand env))

  let map_dst env : dst -> dst = function
    | #global as g -> (map_global env g :> dst)
    | #local  as l -> (map_local  env l :> dst)

  let acall env = Option.map ~f:(fun (x, t) -> new_name env x, t)

  let map_op env op =
    let var = map_var env in
    let glo = map_global env in
    let opnd = map_operand env in
    let args = List.map ~f:opnd in
    let rename = new_name env in
    match op with
    | `call (r, f, a, va) -> `call (acall env r, glo f, args a, args va)
    | `vaarg (x, t, y) -> `vaarg (rename x, t, var y)
    | `vastart x -> `vastart (var x)
    | `bop (x, b, l, r) -> `bop (rename x, b, opnd l, opnd r)
    | `uop (x, u, a) -> `uop (rename x, u, opnd a)
    | `sel (x, t, c, l, r) -> `sel (rename x, t, var c, opnd l, opnd r)
    | `alloc (x, n) -> `alloc (rename x, n)
    | `load (x, t, a) -> `load (rename x, t, opnd a)
    | `store (t, v, a) -> `store (t, opnd v, opnd a)

  let rename_insns env b =
    Blk.insns b |> Seq.map ~f:(fun i ->
        Insn.op i |> map_op env |>
        Insn.create ~label:(Insn.label i)) |>
    Seq.to_list

  let map_tbl env =
    Ctrl.Table.map_exn ~f:(fun v l -> v, map_local env l)

  let swindex env = function
    | `var x -> `var (map_var env x)
    | `sym _ as s -> s

  let rename_ctrl env b =
    let var = map_var env in
    let dst = map_dst env in
    let loc = map_local env in
    let opnd = map_operand env in
    match Blk.ctrl b with
    | `hlt -> `hlt
    | `jmp d -> `jmp (dst d)
    | `br (c, t, f) -> `br (var c, dst t, dst f)
    | `ret r -> `ret (Option.map r ~f:opnd)
    | `sw (t, i, d, tbl) -> `sw (t, swindex env i, loc d, map_tbl env tbl)

  let pop_defs env b =
    let pop x = Var.base x |> Hashtbl.change env.stk ~f:(function
        | Some ([] | [_]) | None -> None
        | Some (_ :: xs) -> Some xs) in
    Blk.args b |> Seq.map ~f:fst |> Seq.iter ~f:pop;
    Blk.insns b |> Seq.filter_map ~f:Insn.lhs |> Seq.iter ~f:pop

  let rec rename_block env l =
    let b = find_blk env l in
    (* Rename the variables in the block. *)
    Option.iter b ~f:(fun b ->
        let args = rename_args env b in
        let insns = rename_insns env b in
        let ctrl = rename_ctrl env b in
        let b = Blk.create ~args ~insns ~ctrl ~label:l () in
        Hashtbl.set env.blks ~key:l ~data:b);
    (* Repeat for the children in the dominator tree. *)
    Tree.children env.dom l |> Seq.iter ~f:(rename_block env);
    (* Pop the renamed variables from the stack. *)
    Option.iter b ~f:(pop_defs env)

  let go env = rename_block env Label.pseudoentry
end

let try_ fn f = try f () with
  | Missing_blk l ->
    Or_error.errorf
      "SSA: missing block %a in function $%s"
      Label.pps l (Func.name fn)
  | Type_error err ->
    Or_error.errorf "SSA: type error: %s" @@
    Error.to_string_hum err

let run typs fn = try_ fn @@ fun () ->
  let env = init fn typs in
  Phi.go env;
  Rename.go env;
  Hashtbl.data env.blks |>
  Func.update_blks fn |>
  Or_error.return
