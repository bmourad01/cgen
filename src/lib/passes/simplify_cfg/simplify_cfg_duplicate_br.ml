(* If we have:

   @blk1:
     ...
     br %c, @blk2, @blk3
   @blk2:
     br %c, @blk4, @blk5

   And @blk2's only predecessor is @blk1, then we can
   transform into:

   @blk1:
     ...
     br %c, @blk4, @blk3

   Because @blk5 will never be reachable from @blk2.

   The same can be done with the inverse case. Given:

   @blk1:
     ...
     br %c, @blk2, @blk3
   @blk3:
     br %c, @blk4, @blk5

   We get:

   @blk1:
     ...
     br %c, @blk2, @blk5
*)

open Core
open Monads.Std
open Virtual
open Simplify_cfg_common

module O = Monad.Option
module Short_circ = Simplify_cfg_short_circ

open O.Let

let is_dup env l c c' =
  Var.(c = c') && Cfg.Node.degree ~dir:`In l env.cfg = 1

let true_br env c y n = match y with
  | `label (y, []) ->
    let* b' = Hashtbl.find env.blks y in
    let* () = O.guard @@ Short_circ.is_empty b' in
    begin match Blk.ctrl b' with
      | `br (c', y', _) when is_dup env y c c' ->
        Some (`br (c, y', n))
      | _ -> None
    end
  | _ -> None

let false_br env c y n = match n with
  | `label (n, []) ->
    let* b' = Hashtbl.find env.blks n in
    let* () = O.guard @@ Short_circ.is_empty b' in
    begin match Blk.ctrl b' with
      | `br (c', _, n') when is_dup env n c c' ->
        Some (`br (c, y, n'))
      | _ -> None
    end
  | _ -> None

let merge_br (`br (c, y, _)) (`br (c', _, n)) =
  assert Var.(c = c');
  `br (c, y, n)

let collect env =
  Hashtbl.fold env.blks ~init:Label.Tree.empty
    ~f:(fun ~key ~data:b acc -> match Blk.ctrl b with
        | `br (c, y, n) ->
          Option.merge (true_br env c y n) (false_br env c y n) ~f:merge_br |>
          Option.value_map ~default:acc ~f:(fun br ->
              Label.Tree.set acc ~key ~data:br)
        | _ -> acc)

let redir changed env dups =
  Hashtbl.mapi_inplace env.blks
    ~f:(fun ~key ~data:b ->
        Label.Tree.find dups key |>
        Option.value_map ~default:b ~f:(fun c ->
            changed := true; Blk.with_ctrl b (c :> ctrl)))

let run env =
  let changed = ref false in
  let dups = collect env in
  if not @@ Label.Tree.is_empty dups then
    redir changed env dups;
  !changed
