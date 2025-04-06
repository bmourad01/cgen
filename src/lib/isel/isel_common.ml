open Core
open Graphlib.Std
open Virtual.Abi

module Id = Isel_internal.Id
module P = Isel_internal.Pattern
module S = Isel_internal.Subst

type 'r node =
  | N of P.op * Id.t list
  | Rv of 'r
  | Tbl of Label.t * (Bv.t * Label.t) list
  | Callargs of 'r list
[@@deriving compare, equal, sexp]

type ty = [Type.basic | `flag | `v128]

(* XXX: maybe we should let the machine implementation decide this. *)
let regcls : ty -> Machine_regvar.cls = function
  | #Type.imm | `flag -> GPR
  | #Type.fp | `v128 -> FP

type 'r t = {
  fn    : func;
  node  : 'r node Vec.t;
  typs  : ty Uopt.t Vec.t;
  cfg   : Cfg.t;
  dom   : Label.t tree;
  rpo   : Label.t -> int;
  blks  : blk Label.Tree.t;
  v2id  : Id.t Var.Table.t;
  id2r  : 'r Id.Table.t;
  insn  : Id.t list Label.Table.t;
  extra : Label.t list Label.Table.t;
  frame : bool;
}

exception Missing_rpo of Label.t

let new_node ?l ?ty t n : Id.t =
  let id = Vec.length t.node in
  assert (id = Vec.length t.typs);
  Vec.push t.node n;
  Vec.push t.typs @@ Uopt.of_option ty;
  Option.iter l ~f:(fun key ->
      Hashtbl.add_multi t.insn ~key ~data:id);
  id

let node t id = Vec.get_exn t.node id
let typeof t id = Uopt.to_option @@ Vec.get_exn t.typs id

let rec pp_node t ppr ppf id = match node t id with
  | Rv r -> Format.fprintf ppf "%a" ppr r
  | Tbl (d, tbl) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    let pp_elt ppf (v, l) =
      Format.fprintf ppf "(%a %a)" Bv.pp v Label.pp l in
    Format.fprintf ppf "(tbl %a [%a])"
      Label.pp d
      (Format.pp_print_list ~pp_sep pp_elt)
      tbl
  | Callargs rs ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(callargs %a)"
      (Format.pp_print_list ~pp_sep ppr)
      rs
  | N (o, []) -> Format.fprintf ppf "%a" P.pp_op o
  | N (o, cs) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)"
      P.pp_op o
      (Format.pp_print_list ~pp_sep (pp_node t ppr))
      cs

let infer_ty_binop : Insn.binop -> ty = function
  | `add t
  | `div t
  | `mul t
  | `sub t -> (t :> ty)
  | `rem t
  | `mulh t
  | `udiv t
  | `umulh t
  | `urem t
  | `and_ t
  | `or_ t
  | `asr_ t
  | `lsl_ t
  | `lsr_ t
  | `rol t
  | `ror t
  | `xor t -> (t :> ty)
  | #Virtual.Insn.cmp -> `flag

let infer_ty_unop : Insn.unop -> ty = function
  | `neg t
  | `copy t -> (t :> ty)
  | `clz t
  | `ctz t
  | `not_ t
  | `popcnt t
  | `flag t
  | `ftosi (_, t)
  | `ftoui (_, t)
  | `itrunc t
  | `sext t
  | `zext t -> (t :> ty)
  | `ifbits t -> (t :> ty)
  | `fext t
  | `fibits t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) -> (t :> ty)
