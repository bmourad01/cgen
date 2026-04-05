open Core
open Regular.Std
open Virtual

let is_tail_ctrl ~blk ~ctrl ~ret =
  let rec go vis ret ctrl = match ctrl, ret with
    | `ret None, None -> true
    | `ret Some `var xr, Some r -> Var.equal xr r
    | `ret _, _ -> false
    | `jmp `label (dst, jargs), _ ->
      not (Label.Tree_set.mem vis dst) && follow vis dst jargs
    | _ -> false
  and follow vis dst jargs = match blk dst with
    | None -> false
    | Some b' when not (Seq.is_empty (Blk.insns b')) -> false
    | Some b' ->
      let vis' = Label.Tree_set.add vis dst in
      let ret' = Option.bind ret ~f:(fun xr ->
          Blk.args b' |> Seq.findi ~f:(fun i _ ->
              match List.nth jargs i with
              | Some `var v -> Var.equal v xr
              | _ -> false) |> Option.map ~f:snd) in
      match ret, ret' with
      | Some _, None -> false
      | _ -> go vis' ret' (Blk.ctrl b') in
  go Label.Tree_set.empty ret ctrl
