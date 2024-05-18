open Core
open Virtual

(* A variable can have one or many values. *)
type value =
  | One of operand
  | Many
[@@deriving equal]

module Phis = Phi_values.Make(struct
    type t = value [@@deriving equal]
    let one v = One v
    let join x y = if equal x y then x else Many
  end)

let filter_many = Map.filter_map ~f:(function
    | Many -> None | One v -> Some v)

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let s = filter_many @@ Phis.analyze ~blk:(Label.Tree.find blks) cfg in
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
