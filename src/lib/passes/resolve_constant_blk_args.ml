open Core
open Virtual
open Phi_values

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

module V = Make(struct
    module Ctrl = struct
      type t = ctrl
      let locals = (locals Ctrl.Table.enum :> t -> _)
    end
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)(D)

module A = Make(struct
    open Abi
    module Ctrl = struct
      type t = ctrl
      let locals = (locals Ctrl.Table.enum :> t -> _)
    end
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)(D)

let check_ssa msg n d fn f =
  if Dict.mem (d fn) Tags.ssa then Ok (f ()) else
    Or_error.errorf
      "In Resolve_constant_blk_args%s: function $%s is \
       not in SSA form" msg (n fn)

let apply fn cfg mb analyze map_blks map_blk with_ctrl with_insns =
  let cfg = cfg fn in
  let blks = mb fn in
  let s = Map.filter_map ~f:Fn.id @@
    analyze ~blk:(Label.Tree.find blks) cfg in
  if not @@ Map.is_empty s then map_blks fn ~f:(fun b ->
      let is, k = map_blk s b in
      with_ctrl (with_insns b is) k)
  else fn
[@@specialise]

let run fn =
  check_ssa "" Func.name Func.dict fn @@ fun () ->
  apply fn
    Cfg.create
    Func.map_of_blks
    V.analyze
    Func.map_blks
    Subst_mapper.map_blk
    Blk.with_ctrl
    Blk.with_insns

let run_abi fn =
  let open Abi in
  check_ssa " (ABI)" Func.name Func.dict fn @@ fun () ->
  apply fn
    Cfg.create
    Func.map_of_blks
    A.analyze
    Func.map_blks
    Subst_mapper_abi.map_blk
    Blk.with_ctrl
    Blk.with_insns
