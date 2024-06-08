open Core
open Regular.Std
open Virtual
open Simplify_cfg_common

let is_empty = Fn.compose Seq.is_empty Blk.insns

let collect_cond_phi env =
  Hashtbl.fold env.blks ~init:Label.Tree.empty
    ~f:(fun ~key ~data:b acc ->
        if is_empty b then match Blk.ctrl b with
          | `br (c, y, n) when Blk.has_arg b c ->
            Label.Tree.set acc ~key ~data:(y, n);
          | _ -> acc
        else acc)

let is_var x = function
  | `var y -> Var.(x = y)
  | _ -> false

let brcond cphi c = function
  | `label (l, args) when List.exists args ~f:(is_var c) ->
    Label.Tree.find cphi l
  | _ -> None
    
let redir changed env cphi =
  Hashtbl.map_inplace env.blks ~f:(fun b ->
      match Blk.ctrl b with
      | `br (c, y, n) ->
        let y' =
          brcond cphi c y |>
          Option.value_map ~default:y ~f:(fun (y, _) ->
              changed := true; y) in
        let n' =
          brcond cphi c n |>
          Option.value_map ~default:n ~f:(fun (_, n) ->
              changed := true; n) in
        Blk.with_ctrl b @@ `br (c, y', n')
      | _ -> b)

let run env =
  let changed = ref false in
  let cphi = collect_cond_phi env in
  if not @@ Label.Tree.is_empty cphi then
    redir changed env cphi;
  !changed
