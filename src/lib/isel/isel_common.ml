open Core
open Graphlib.Std
open Virtual.Abi

module P = Isel_internal.Pattern
module Id = Int

type id = Id.t [@@deriving compare, equal, hash, sexp]

type 'r node =
  | N of P.op * id list
  | Rv of 'r
[@@deriving compare, equal, hash, sexp]

type ty = [Type.basic | `flag | `v128]

type 'r t = {
  fn    : func;
  node  : 'r node Vec.t;
  typs  : ty Uopt.t Vec.t;
  cfg   : Cfg.t;
  dom   : Label.t tree;
  rpo   : Label.t -> int;
  blks  : blk Label.Tree.t;
  v2id  : id Var.Table.t;
  id2r  : 'r Id.Table.t;
  insn  : id Ftree.t Label.Table.t;
  extra : Label.t list Label.Table.t;
}

exception Missing_rpo of Label.t

let new_node ?l ?ty t n : id =
  let id = Vec.length t.node in
  assert (id = Vec.length t.typs);
  Vec.push t.node n;
  Vec.push t.typs @@ Uopt.of_option ty;
  Option.iter l ~f:(Hashtbl.update t.insn ~f:(function
      | Some ids -> Ftree.snoc ids id
      | None -> Ftree.singleton id));
  id

let node t id = Vec.get_exn t.node id
let typeof t id = Uopt.to_option @@ Vec.get_exn t.typs id

let rec pp_node t ppr ppf id = match node t id with
  | Rv r -> Format.fprintf ppf "%a" ppr r
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
  | `rem t
  | `sub t -> (t :> ty)
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
