open Core
open Regular.Std
open Graphlib.Std

type state = Var.Set.t [@@deriving equal]

let empty_state : state = Var.Set.empty

(* Starting constraint has the entry block with no incoming
   initializations. *)
let init_constraints : state Label.Map.t =
  Label.Map.singleton Label.pseudoentry empty_state

(* Our top element, which is every slot having been initialized. *)
let top_state slots : state =
  Var.Set.of_list @@ Map.keys slots

(* Since this is a "must" forward-flow analysis, incoming
   predecessor states must intersect. *)
let merge_state = Set.inter

type solution = (Label.t, state) Solution.t

type t = {
  soln : solution;
  bad  : Label.Hash_set.t;
}

module Make(M : Scalars.L) = struct
  open M

  module Analysis = Scalars.Make(M)

  let transfer_store acc ptr (s : Scalars.state) =
    match Map.find s ptr with
    | Some Offset (base, _) -> Set.add acc base
    | _ -> acc

  let transfer_load bad acc l ptr (s : Scalars.state) =
    match Map.find s ptr with
    | Some Offset (base, _) ->
      (* If the slot is not always initialized by the
         time we reach the load, then we have UB. *)
      if not @@ Set.mem acc base then Hash_set.add bad l;
      acc
    | _ -> acc

  let transfer bad t blks slots l st =
    match Label.Tree.find blks l with
    | None -> st
    | Some b ->
      let s = ref @@ Scalars.get t l in
      Blk.insns b |> Seq.fold ~init:st ~f:(fun acc i ->
          let op = Insn.op i and l = Insn.label i in
          let acc = match Insn.load_or_store_to op with
            | Some (ptr, _, Store) -> transfer_store acc ptr !s
            | Some (ptr, _, Load) -> transfer_load bad acc l ptr !s
            | _ -> acc in
          s := Analysis.transfer_op slots !s op;
          acc)

  let analyze cfg blks slots =
    let t = Analysis.analyze cfg blks slots in
    let bad = Label.Hash_set.create () in
    let s = Graphlib.fixpoint (module Cfg) cfg
        ~init:(Solution.create init_constraints @@ top_state slots)
        ~start:Label.pseudoentry
        ~equal:equal_state
        ~merge:merge_state
        ~f:(transfer bad t blks slots) in
    Logs.debug (fun m ->
        Label.Tree.iter blks ~f:(fun ~key ~data:_ ->
            let s = Solution.get s key in
            m "%s: %a: incoming must-initialize: %s%!"
              __FUNCTION__ Label.pp key
              (Set.to_list s |> List.to_string ~f:Var.to_string)));
    Logs.debug (fun m ->
        Hash_set.iter bad ~f:(fun l ->
            m "%s: load at %a is potentially uninitialized%!"
              __FUNCTION__ Label.pp l));
    {soln = s; bad}
end
