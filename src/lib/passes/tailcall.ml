open Core
open Regular.Std
open Virtual

let make_tailcall b i x f args vargs =
  Insn.label i |>
  Blk.remove_insn b |>
  Blk.map_ctrl ~f:(fun _ ->
      let ty = Option.map x ~f:snd in
      `tcall (ty, f, args, vargs))

let can_tail i = not @@ Dict.mem (Insn.dict i) Insn.Tag.non_tail

let run fn = Func.map_blks fn ~f:(fun b ->
    (* This should only be doable if a call is the last
       instruction in the block, before the terminator.
       Any pure operations that are computed afterward
       would have been removed if they did not contribute
       to the result of the function. On the other hand,
       side-effecting operations would also need to run
       if they came after the call. *)
    match Seq.hd @@ Blk.insns b ~rev:true with
    | None -> b
    | Some i -> match Insn.op i with
      | `call (x, f, args, vargs) when can_tail i ->
        begin match Blk.ctrl b with
          | `ret None -> make_tailcall b i x f args vargs
          | `ret Some (`var y) ->
            begin match x with
              | Some (x', _) when Var.(x' = y) ->
                make_tailcall b i x f args vargs
              | None | Some _ -> b
            end
          | _ -> b
        end
      | _ -> b)
