open Core
open Virtual

module Phis = Phi_values.Make(struct
    (* `None` indicates that there may be many values for the phi,
       while `Some v` indicates that `v` is its singular value.

       We choose `option` because filtering the substitution produced
       by the analysis can use the identity function via `Map.filter_map`,
       thus avoiding extra allocations.
    *)
    type t = operand option [@@deriving equal]

    let one v = Some v
    let join x y = if equal x y then x else None
  end)

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let s =
      Map.filter_map ~f:Fn.id @@
      Phis.analyze ~blk:(Label.Tree.find blks) cfg in
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
