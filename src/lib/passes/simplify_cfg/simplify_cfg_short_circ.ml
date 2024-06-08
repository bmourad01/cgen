open Core
open Monads.Std
open Regular.Std
open Virtual
open Simplify_cfg_common

module O = Monad.Option

open O.Let

let is_empty = Fn.compose Seq.is_empty Blk.insns

let cmp_ne b = match Seq.next @@ Blk.insns b with
  | Some (i, is) when Seq.is_empty is ->
    begin match Insn.op i with
      | `bop (k, `ne _, `var v, `int (n, _))
      | `bop (k, `ne _, `int (n, _), `var v)
        when Bv.(n = zero) -> Some (k, v)
      | _ -> None
    end
  | _ -> None

let argidx b c =
  Blk.args b |>
  Seq.findi ~f:(fun _ -> Var.equal c) |>
  Option.map ~f:fst

let collect_cond_phi env =
  Hashtbl.fold env.blks ~init:Label.Tree.empty
    ~f:(fun ~key ~data:b acc ->
        if is_empty b then match Blk.ctrl b with
          | `br (c, y, n) ->
            argidx b c |> Option.value_map ~default:acc ~f:(fun i ->
                Label.Tree.set acc ~key ~data:(y, n, i))
          | _ -> acc
        else match cmp_ne b with
          | None -> acc
          | Some (k, v) -> match Blk.ctrl b with
            | `br (c, y, n) when Var.(c = k) ->
              argidx b v |> Option.value_map ~default:acc ~f:(fun i ->
                  Label.Tree.set acc ~key ~data:(y, n, i))
            | _ -> acc)

let is_var env x = function
  | `var y ->
    Var.(x = y) ||
    Hashtbl.find env.flag y |>
    Option.value_map ~default:false ~f:(Var.equal x)
  | _ -> false

let brcond env cphi c = function
  | `label (l, args) ->
    let* y, n, i = Label.Tree.find cphi l in
    let* arg = List.nth args i in
    let+ () = O.guard @@ is_var env c arg in
    y, n
  | _ -> None

let redir changed env cphi =
  Hashtbl.map_inplace env.blks ~f:(fun b ->
      match Blk.ctrl b with
      | `br (c, y, n) ->
        let y' =
          brcond env cphi c y |>
          Option.value_map ~default:y ~f:(fun (y, _) ->
              changed := true; y) in
        let n' =
          brcond env cphi c n |>
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
