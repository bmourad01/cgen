open Core
open Regular.Std
open Ssa_impl_common

(* Second phase of the algorithm is to traverse the dominator tree
   and rename variables in each block according to their use-def
   chains. *)
module Make(M : L) : sig
  val go : (M.Live.t, M.Cfg.t, M.Blk.t) env -> alloc:(unit -> Var.t) -> unit
end = struct
  open M

  let find_blk env l = match LT.find env.blks l with
    | None when Label.is_pseudo l -> None
    | None -> raise_notrace @@ Missing_blk l
    | Some _ as b -> b

  let new_name stk alloc x =
    let y = alloc () in
    VT.add_multi stk ~key:x ~data:y;
    y

  (* NB: `new_name` allocates fresh variables, so the traversal must be
     forward to keep variable numbering stable. *)
  let rename_args stk alloc b =
    Blk.fold_args b ~init:[] ~f:(fun acc x ->
        new_name stk alloc x :: acc) |> List.rev

  let map_var stk x = match VT.find stk x with
    | Some [] | None -> x
    | Some (y :: _) -> y

  let rename_insns stk alloc b =
    let rename = new_name stk alloc in
    let stk = map_var stk in
    Blk.fold_insns b ~init:[] ~f:(fun acc i ->
        let i' =
          Insn.op i |>
          rename_op ~stk ~rename |>
          Insn.with_op i in
        i' :: acc) |>
    List.rev

  let pop_var stk x =
    VT.change stk x ~f:(function
        | Some ([] | [_]) | None -> None
        | Some (_ :: xs) -> Some xs)

  let pop_defs stk b =
    let f = pop_var stk in
    Blk.iter_args b ~f;
    Blk.iter_insns b ~f:(fun i -> List.iter (Insn.lhs i) ~f)

  type action =
    | Visit of Label.t
    | Pop of Blk.t

  let visit q env stk alloc l =
    find_blk env l |> Option.iter ~f:(fun b ->
        (* Rename the variables in the block. *)
        let dict = Blk.dict b in
        let args = rename_args stk alloc b in
        let insns = rename_insns stk alloc b in
        let ctrl = rename_ctrl ~stk:(map_var stk) @@ Blk.ctrl b in
        let b' = Blk.create ~dict ~args ~insns ~ctrl ~label:l () in
        LT.set env.blks ~key:l ~data:b';
        (* Pop the renamed variables from the stack. *)
        Stack.push q @@ Pop b);
    (* Repeat for the children in the dominator tree. *)
    Semi_nca.Tree.children env.dom l |> Seq.iter
      ~f:(fun l -> Stack.push q @@ Visit l)

  let go env ~alloc =
    let stk = VT.create ~capacity:env.nvars () in
    let q = Stack.singleton @@ Visit Label.pseudoentry in
    Stack.until_empty q @@ function
    | Visit l -> visit q env stk alloc l
    | Pop b -> pop_defs stk b
end
