(* Turn tail-recursive calls into jumps. *)

open Core
open Regular.Std
open Virtual
open Simplify_cfg_common

open Context.Syntax

let collect_calls env fn =
  let name = Func.name fn in
  Func.blks fn |> Seq.fold ~init:Label.Tree.empty ~f:(fun acc b ->
      match Seq.hd @@ Blk.insns ~rev:true b with
      | None -> acc
      | Some i -> match Insn.op i with
        | `call (r, `sym (f, 0), args, []) when String.(f = name) ->
          begin match r, Blk.ctrl b with
            | None, `ret Some _ | Some _, `ret None -> acc
            (* The result of the function isn't used as the return value. *)
            | Some (x, _), `ret Some `var y when Var.(x <> y) -> acc
            | Some (x, _), `jmp (`label (l, [`var y]))
              when is_ret env l && Var.(x <> y) -> acc
            (* Normal case. *)
            | Some _, `ret Some `var _
            | None, `ret None ->
              Label.Tree.set acc ~key:(Blk.label b) ~data:(args, Insn.label i)
            (* Accounting for the case where we merged all `ret`s. *)
            | Some _, `jmp `label (l, [_])
            | None, `jmp `label (l, []) when is_ret env l ->
              Label.Tree.set acc ~key:(Blk.label b) ~data:(args, Insn.label i)
            | _ -> acc
          end
        | _ -> acc)

let fresh_args fn =
  Func.args fn |> Context.Seq.fold
    ~init:([], Var.Map.empty)
    ~f:(fun (l, m) (x, _) ->
        let+ y = Context.Var.fresh in
        y :: l, Map.set m ~key:x ~data:(`var y))

let subst_args subst b =
  let insns, ctrl = Subst_mapper.map_blk subst b in
  insns |> Blk.with_insns b |> Fn.flip Blk.with_ctrl ctrl

let redir_entry e calls b = match Label.Tree.find calls @@ Blk.label b with
  | Some (args, l) ->
    Blk.remove_insn b l |>
    Fn.flip Blk.with_ctrl (`jmp (`label (e, args)))
  | None -> b

let new_entry fn e =
  let args =
    Func.args fn |>
    Seq.map ~f:(fun (x, _) -> `var x) |>
    Seq.to_list in
  Context.Virtual.blk ~ctrl:(`jmp (`label (e, args))) ()

let unless fn b k = if b then !!fn else k ()

let go env fn =
  unless fn (Func.variadic fn) @@ fun () ->
  let calls = collect_calls env fn in
  unless fn (Label.Tree.is_empty calls) @@ fun () ->
  let* args, subst = fresh_args fn in
  let e = Func.entry fn in
  let blks =
    Func.blks fn |> Seq.map ~f:(subst_args subst) |>
    Seq.map ~f:(redir_entry e calls) |>
    Seq.to_list |> function
    | [] -> assert false
    | e :: rest ->
      assert (Seq.is_empty @@ Blk.args e);
      List.fold args ~init:e ~f:Blk.prepend_arg :: rest in
  let* h = new_entry fn e in
  let*? fn = Func.with_blks fn (h :: blks) in
  !!fn
