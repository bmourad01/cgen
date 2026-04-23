open Core
open Virtual.Abi
open Cgen_containers

module Id = Isel_internal.Id
module P = Isel_internal.Pattern
module S = Isel_internal.Subst
module LT = Label.Dense_table
module VT = Var.Dense_table

type 'r node =
  | N of P.op * Id.t list
  | Rv of 'r
  | Tbl of Label.t * (Bv.t * Label.t) list
  | Callargs of 'r list
[@@deriving compare, equal, sexp]

type ty = [Type.basic | `flag | `v128]

type 'r t = {
  fn             : func;
  node           : 'r node Vec.t;
  typs           : ty Uopt.t Vec.t;
  id2r           : 'r Uopt.t Vec.t;
  cfg            : Cfg.t;
  dom            : Semi_nca.tree;
  blks           : blk Label.Tree.t;
  v2id           : Id.t VT.t;
  insn           : Id.t list LT.t;
  extra          : Label.t list LT.t;
  frame          : bool;
  loadgen        : (int * Id.t) VT.t;
  mutable phi    : Var.Set.t;
  mutable memgen : int;
}

let new_node ?l ?ty t n : Id.t =
  let id = Vec.length t.node in
  assert (id = Vec.length t.typs);
  Vec.push t.node n;
  Vec.push t.typs @@ Uopt.of_option ty;
  Vec.push t.id2r Uopt.none;
  Option.iter l ~f:(fun key ->
      LT.add_multi t.insn ~key ~data:id);
  id

let node t id = Vec.get_exn t.node id
let typeof t id = Uopt.to_option @@ Vec.get_exn t.typs id
let setvar t x id = VT.set t.v2id ~key:x ~data:id
let getvar t x = VT.find t.v2id x
let setrv t id r = Vec.set_exn t.id2r id @@ Uopt.some r
let getrv t id = Uopt.to_option @@ Vec.get_exn t.id2r id
let addextra t key data = LT.add_multi t.extra ~key ~data

let newvar ~f t x ty = VT.find_or_add t.v2id x ~default:(fun () ->
    let v = f x in
    let id = new_node ~ty t @@ Rv v in
    setrv t id v;
    id)

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
