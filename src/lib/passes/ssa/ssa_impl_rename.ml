open Core
open Regular.Std
open Graphlib.Std
open Ssa_impl_common

(* Second phase of the algorithm is to traverse the dominator tree
   and rename variables in each block according to their use-def
   chains. *)
module Make(M : L) : sig
  val go : (M.Live.t, M.Cfg.t, M.Blk.t) env -> unit
end = struct
  open M

  let find_blk env l = match Hashtbl.find env.blks l with
    | None when Label.is_pseudo l -> None
    | None -> raise_notrace @@ Missing_blk l
    | Some _ as b -> b

  let new_name stk nums x =
    let key = Var.base x in
    let default = 1 in
    let n = ref default in
    let upd x = n := x + 1; !n in
    Hashtbl.update nums key ~f:(Option.value_map ~default ~f:upd);
    let y = Var.with_index x !n in
    Hashtbl.add_multi stk ~key ~data:y;
    y

  let rename_args stk nums b =
    Blk.args b |> Seq.map ~f:(new_name stk nums) |> Seq.to_list

  let map_var stk x = match Hashtbl.find stk x with
    | Some [] | None -> x
    | Some (y :: _) -> y

  let rename_insns stk nums b =
    let rename = new_name stk nums in
    let stk = map_var stk in
    Blk.insns b |> Seq.map ~f:(fun i ->
        Insn.op i |> rename_op ~stk ~rename |> Insn.with_op i) |>
    Seq.to_list

  let pop_var stk x =
    Var.base x |> Hashtbl.change stk ~f:(function
        | Some ([] | [_]) | None -> None
        | Some (_ :: xs) -> Some xs)

  let pop_defs stk b =
    let f = pop_var stk in
    Blk.args b |> Seq.iter ~f;
    Blk.insns b |> Seq.map ~f:Insn.lhs |>
    Seq.iter ~f:(List.iter ~f)

  type action =
    | Visit of Label.t
    | Pop of Blk.t

  let visit q env nums stk l =
    find_blk env l |> Option.iter ~f:(fun b ->
        (* Rename the variables in the block. *)
        let dict = Blk.dict b in
        let args = rename_args stk nums b in
        let insns = rename_insns stk nums b in
        let ctrl = rename_ctrl ~stk:(map_var stk) @@ Blk.ctrl b in
        let b' = Blk.create ~dict ~args ~insns ~ctrl ~label:l () in
        Hashtbl.set env.blks ~key:l ~data:b';
        (* Pop the renamed variables from the stack. *)
        Stack.push q @@ Pop b);
    (* Repeat for the children in the dominator tree. *)
    Tree.children env.dom l |> Seq.iter
      ~f:(fun l -> Stack.push q @@ Visit l)

  let go env =
    (* Current version of each variable. *)
    let stk = Var.Table.create () in
    (* Freshener for variable versions. *)
    let nums = Var.Table.create () in
    let q = Stack.singleton @@ Visit Label.pseudoentry in
    Stack.until_empty q @@ function
    | Visit l -> visit q env nums stk l
    | Pop b -> pop_defs stk b
end
