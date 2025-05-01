(* Collapse a two-case switch (including default) into a conditional
   branch. *)

open Core
open Regular.Std
open Virtual

open Context.Syntax

let go fn =
  let+ bs = Func.blks fn |> Context.Seq.filter_map ~f:(fun b ->
      match Blk.ctrl b with
      | `sw (t, i, d, tbl) when Ctrl.Table.length tbl = 1 ->
        let v, k = Seq.hd_exn @@ Ctrl.Table.enum tbl in
        let+ c, cmp = Context.Virtual.binop
            (`eq (t :> Type.basic))
            (i :> operand)
            (`int (v, t)) in
        let b = Blk.append_insn b cmp in
        Some (Blk.with_ctrl b @@ `br (c, (k :> dst), (d :> dst)))
      | _ -> !!None) >>| Seq.to_list in
  Func.update_blks_exn fn bs
