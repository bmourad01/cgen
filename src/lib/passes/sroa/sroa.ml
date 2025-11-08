open Core
open Virtual
open Sroa_impl

let var_set_of_option = function
  | Some x -> Var.Set.singleton x
  | None -> Var.Set.empty

let offset = function
  | `bop (_, `add _, `var x, `int (i, _))
  | `bop (_, `add _, `int (i, _), `var x) ->
    Some (x, Bv.to_int64 i)
  | `bop (_, `sub _, `var x, `int (i, _)) ->
    Some (x, Int64.neg @@ Bv.to_int64 i)
  | _ -> None

(* TODO: more cases? *)
let copy_of = function
  | `uop (_, `copy _, `var x) -> Some x
  | `bop (_, `add _, `var x, `int (i, _))
  | `bop (_, `add _, `int (i, _), `var x)
  | `bop (_, `sub _, `var x, `int (i, _))
    when Bv.(i = zero) -> Some x
  | _ -> None

let escapes mty fv = function
  | `store (ty, `var x, `var y) when mty ty -> Var.Set.of_list [x; y]
  | `store (_, `var x, _) -> Var.Set.singleton x
  | `load (_, ty, `var x) when mty ty -> Var.Set.singleton x
  | `load _ -> Var.Set.empty
  | o when Option.is_some (offset o) -> Var.Set.empty
  | o when Option.is_some (copy_of o) -> Var.Set.empty
  | o -> fv o
[@@specialise]

let load_or_store_to o = match o with
  | `load (_, (#Type.basic as b), `var x) -> Some (x, b, Load)
  | `store ((#Type.basic as b), _, `var x) -> Some (x, b, Store)
  | _ -> None

let subst_load_or_store o ~f = match o with
  | `load (x, (#Type.basic as b), `var a) -> `load (x, b, `var (f a))
  | `store ((#Type.basic as b), v, `var a) -> `store (b, v, `var (f a))
  | op -> op

let add x ty b o =
  assert Int64.(o > 0L);
  let i = Bv.(int64 o mod modulus (Type.sizeof_imm_base ty)) in
  `bop (x, `add (ty :> Type.basic), `var b, `int (i, (ty :> Type.imm)))

let is_named = function
  | `name _ -> true
  | _ -> false

module V = Make(struct
    module Insn = struct
      type t = Insn.t
      type op = Insn.op

      let create ~label op = Insn.create op ~label
      let with_op = Insn.with_op

      let op = Insn.op
      let label = Insn.label
      let lhs = Insn.lhs_of_op
      let offset = (offset :> op -> _)
      let copy_of = (copy_of :> op -> _)
      let fv = Insn.free_vars_of_op
      let escapes = (escapes is_named fv :> op -> _)
      let load_or_store_to = (load_or_store_to :> op -> _)
      let subst_load_or_store ~f = (subst_load_or_store ~f :> op -> _)
      let add x ty b o = (add x ty b o :> op)
    end

    module Ctrl = struct
      type t = ctrl
      let escapes = Ctrl.free_vars
    end

    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)

module A = Make(struct
    open Abi

    module Insn = struct
      type t = Insn.t
      type op = Insn.op

      let create ~label op = Insn.create op ~label
      let with_op = Insn.with_op

      let op = Insn.op
      let label = Insn.label

      let lhs = function
        | `bop (x, _, _, _)
        | `uop (x, _, _)
        | `sel (x, _, _, _, _)
        | `load (x, _, _)
          -> Some x
        | _ -> None

      let offset = (offset :> op -> _)
      let copy_of = (copy_of :> op -> _)
      let fv = Insn.free_vars_of_op
      let escapes = (escapes (const false) fv :> op -> _)
      let load_or_store_to = (load_or_store_to :> op -> _)
      let subst_load_or_store ~f = (subst_load_or_store ~f :> op -> _)
      let add x ty b o = (add x ty b o :> op)
    end

    module Ctrl = struct
      type t = ctrl
      (* TODO: see if we can relax passing of block params *)
      let escapes = Ctrl.free_vars
    end

    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)

open Context.Syntax

let run fn =
  let* () = Context.unless (Dict.mem (Func.dict fn) Tags.ssa) @@ fun () ->
    Context.failf "In SROA: function $%s is not in SSA form"
      (Func.name fn) () in
  V.run fn

let run_abi fn =
  let* () = Context.unless (Dict.mem (Abi.Func.dict fn) Tags.ssa) @@ fun () ->
    Context.failf "In SROA (ABI): function $%s is not in SSA form"
      (Abi.Func.name fn) () in
  A.run fn
