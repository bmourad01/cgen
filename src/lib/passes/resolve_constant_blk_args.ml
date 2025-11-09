open Core
open Regular.Std
open Virtual

let table enum d ds tbl =
  enum tbl |> Seq.map ~f:snd |>
  Seq.map ~f:(fun (`label (l, args)) -> l, args) |>
  Seq.to_list |> List.cons (d, ds)

let locals enum = function
  | `hlt -> []
  | `jmp #global -> []
  | `jmp `label (l, args) -> [l, args]
  | `br (_, #global, #global) -> []
  | `br (_, `label (y, ys), #global) -> [y, ys]
  | `br (_, #global, `label (n, ns)) -> [n, ns]
  | `br (_, `label (y, ys), `label (n, ns)) -> [y, ys; n, ns]
  | `ret _ -> []
  | `sw (_, _, `label (d, ds), tbl) -> table enum d ds tbl

module D = struct
  (* `None` indicates that there may be many values for the phi,
     while `Some v` indicates that `v` is its singular value.

     We choose `option` because filtering the substitution produced
     by the analysis can use the identity function via `Map.filter_map`,
     thus avoiding extra allocations.
  *)
  type t = operand option [@@deriving equal]

  let one v = Some v
  let join x y = if equal x y then x else None
end

module Phis_v = Phi_values.Make(struct
    module Ctrl = struct
      type t = ctrl
      let locals = (locals Ctrl.Table.enum :> t -> _)
    end
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)(D)

module Phis_a = Phi_values.Make(struct
    open Abi
    module Ctrl = struct
      type t = ctrl
      let locals = (locals Ctrl.Table.enum :> t -> _)
    end
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)(D)

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let s =
      Map.filter_map ~f:Fn.id @@
      Phis_v.analyze ~blk:(Label.Tree.find blks) cfg in
    let fn =
      if not @@ Map.is_empty s then Func.map_blks fn ~f:(fun b ->
          let is, k = Subst_mapper.map_blk s b in
          Blk.(with_ctrl (with_insns b is) k))
      else fn in
    Ok fn
  else
    Or_error.errorf
      "In Resolve_constant_blk_args: function $%s is \
       not in SSA form" (Func.name fn)

let run_abi fn =
  let open Abi in
  if Dict.mem (Func.dict fn) Tags.ssa then
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let s =
      Map.filter_map ~f:Fn.id @@
      Phis_a.analyze ~blk:(Label.Tree.find blks) cfg in
    let fn =
      if not @@ Map.is_empty s then Func.map_blks fn ~f:(fun b ->
          let is, k = Subst_mapper_abi.map_blk s b in
          Blk.(with_ctrl (with_insns b is) k))
      else fn in
    Ok fn
  else
    Or_error.errorf
      "In Resolve_constant_blk_args (ABI): function $%s is \
       not in SSA form" (Func.name fn)
