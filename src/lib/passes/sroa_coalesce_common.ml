open Core
open Regular.Std
open Virtual
open Scalars

let var_set_of_option = function
  | Some x -> Var.Set.singleton x
  | None -> Var.Set.empty

(* Instructions that can produce a scalar `Offset` value. *)
let offset = function
  | `bop (_, `add _, `var x, `int (i, _))
  | `bop (_, `add _, `int (i, _), `var x) ->
    Some (x, Bv.to_int64 i)
  | `bop (_, `sub _, `var x, `int (i, _)) ->
    Some (x, Int64.neg @@ Bv.to_int64 i)
  | _ -> None

(* Instructions that behave like `copy` instead of causing
   a variable to "escape".

   TODO: more cases?
*)
let copy_of = function
  | `uop (_, `copy _, `var x) -> Some x
  | `bop (_, `add _, `var x, `int (i, _))
  | `bop (_, `add _, `int (i, _), `var x)
  | `bop (_, `sub _, `var x, `int (i, _))
    when Bv.(i = zero) -> Some x
  | _ -> None

let escapes mty fv = function
  | `store (ty, `var x, `var y) when mty ty -> Var.Set.of_list [x; y]
  | `store (ty, _, `var y) when mty ty -> Var.Set.of_list [y]
  | `store (_, `var x, _) -> Var.Set.singleton x
  | `store _ -> Var.Set.empty
  | `load (_, ty, `var x) when mty ty -> Var.Set.singleton x
  | `load _ -> Var.Set.empty
  | o when Option.is_some (offset o) -> Var.Set.empty
  | o when Option.is_some (copy_of o) -> Var.Set.empty
  | o -> fv o
[@@specialise]

let load_or_store_to = function
  | `load (_, (#Type.basic as b), `var x) -> Some (x, b, Load)
  | `store ((#Type.basic as b), _, `var x) -> Some (x, b, Store)
  | _ -> None

let replace_load_or_store_addr a = function
  | `load (x, (#Type.basic as b), _) -> `load (x, b, `var a)
  | `store ((#Type.basic as b), v, _) -> `store (b, v, `var a)
  | op -> op

let add x ty b o =
  assert Int64.(o > 0L);
  let i = Bv.(int64 o mod modulus (Type.sizeof_imm_base ty)) in
  `bop (x, `add (ty :> Type.basic), `var b, `int (i, (ty :> Type.imm)))

let is_named = function
  | `name _ -> true
  | _ -> false

let local l args = l, List.filter_map args ~f:var_of_operand

let table enum d ds tbl =
  enum tbl |> Seq.map ~f:snd |>
  Seq.map ~f:(fun (`label (l, args)) -> local l args) |>
  Seq.to_list |> List.cons (local d ds)

let locals enum = function
  | `hlt -> []
  | `jmp #global -> []
  | `jmp `label (l, args) ->
    [local l args]
  | `br (_, #global, #global) -> []
  | `br (_, `label (y, ys), #global) ->
    [local y ys]
  | `br (_, #global, `label (n, ns)) ->
    [local n ns]
  | `br (_, `label (y, ys), `label (n, ns)) ->
    [local y ys; local n ns]
  | `ret _ -> []
  | `sw (_, _, `label (d, ds), tbl) ->
    table enum d ds tbl

let escapes_ctrl fv = function
  | `hlt -> Var.Set.empty
  | `jmp `var x -> Var.Set.singleton x
  | `jmp _ -> Var.Set.empty
  | `br (c, `var y, `var n) -> Var.Set.of_list [c; y; n]
  | `br (c, _, `var n) -> Var.Set.of_list [c; n]
  | `br (c, `var y, _) -> Var.Set.of_list [c; y]
  | `br (c, _, _) -> Var.Set.singleton c
  | `ret _ as c -> fv c
  | `sw (_, `var i, _, _) -> Var.Set.singleton i
  | `sw _ -> Var.Set.empty
[@@specialise]

module VL = struct
  module Insn = struct
    type t = Insn.t
    type op = Insn.op
    let create ~label op = Insn.create op ~label
    let with_op = Insn.with_op
    let op = Insn.op
    let special = function
      | #Insn.variadic -> true
      | _ -> false
    let label = Insn.label
    let lhs = var_set_of_option @. Insn.lhs_of_op
    let offset = (offset :> op -> _)
    let copy_of = (copy_of :> op -> _)
    let free_vars = Insn.free_vars_of_op
    let escapes = (escapes is_named free_vars :> op -> _)
    let load_or_store_to = (load_or_store_to :> op -> _)
    let replace_load_or_store_addr a = (replace_load_or_store_addr a :> op -> _)
    let add x ty b o = (add x ty b o :> op)
  end
  module Ctrl = struct
    type t = ctrl
    let free_vars = Ctrl.free_vars
    let escapes = (escapes_ctrl free_vars :> t -> _)
    let locals = (locals Ctrl.Table.enum :> t -> _)
  end
  module Blk = Blk
  module Func = Func
  module Cfg = Cfg
end

module AL = struct
  open Abi
  module Insn = struct
    type t = Insn.t
    type op = Insn.op
    let create ~label op = Insn.create op ~label
    let with_op = Insn.with_op
    let op = Insn.op
    let special = function
      | #Insn.extra -> true
      | _ -> false
    let label = Insn.label
    let lhs = Insn.def_of_op
    let offset = (offset :> op -> _)
    let copy_of = (copy_of :> op -> _)
    let free_vars = Insn.free_vars_of_op
    let escapes = (escapes (const false) free_vars :> op -> _)
    let load_or_store_to = (load_or_store_to :> op -> _)
    let replace_load_or_store_addr a = (replace_load_or_store_addr a :> op -> _)
    let add x ty b o = (add x ty b o :> op)
  end
  module Ctrl = struct
    type t = ctrl
    let free_vars = Ctrl.free_vars
    let escapes = (escapes_ctrl free_vars :> t -> _)
    let locals = (locals Ctrl.Table.enum :> t -> _)
  end
  module Blk = Blk
  module Func = Func
  module Cfg = Cfg
end
