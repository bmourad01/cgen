open Core
open Graphlib.Std
open Regular.Std
open Monads.Std
open Virtual

exception Occurs_failed of Var.t * Label.t option

module Bitvec = struct
  include Bitvec
  include Bitvec_binprot
  include Bitvec_order
  include Bitvec_sexp
end

type pure =
  | Palloc  of Label.t * int
  | Pbinop  of Label.t * Insn.binop * pure * pure
  | Pcall   of Label.t * Type.basic * global * pure list * pure list
  | Pdouble of float
  | Pflag   of bool
  | Pint    of Bitvec.t * Type.imm
  | Pload   of Label.t * Type.basic * pure
  | Psel    of Label.t * Type.basic * pure * pure * pure
  | Psingle of Float32.t
  | Psym    of string * int
  | Punop   of Label.t * Insn.unop * pure
  | Pvar    of Var.t
[@@deriving bin_io, compare, equal, sexp]

and global =
  | Gaddr of Bitvec.t
  | Gpure of pure
  | Gsym  of string
[@@deriving bin_io, compare, equal, sexp]

and local = Label.t * pure list
[@@deriving bin_io, compare, equal, sexp]

and dst =
  | Dglobal of global
  | Dlocal  of local
[@@deriving bin_io, compare, equal, sexp]

type table = (Bitvec.t * local) list
[@@deriving bin_io, compare, equal, sexp]

type t =
  | Ebr      of pure * dst * dst
  | Ecall    of global * pure list * pure list
  | Ehlt
  | Ejmp     of dst
  | Eret     of pure option
  | Eset     of Var.t * pure
  | Estore   of Type.basic * pure * pure
  | Esw      of Type.imm * pure * local * table
  | Evaarg   of Var.t * Type.basic * Var.t
  | Evastart of Var.t
[@@deriving bin_io, compare, equal, sexp]

module E = Monad.Result.Error

open E.Let
open E.Syntax

module Deps = Graphlib.Make(Label)(Var)

type resolved = [
  | `blk  of blk
  | `insn of insn * blk * Var.t option
]

type ctx = {
  func         : string;
  elts         : resolved Label.Tree.t;
  cfg          : Cfg.t;
  pure         : pure Var.Table.t;
  exp          : t Label.Table.t;
  filled       : Var.Hash_set.t;
  mutable deps : Deps.t;
}

let init_elts fn =
  Func.blks fn |> E.Seq.fold ~init:Label.Tree.empty ~f:(fun t b ->
      let label = Blk.label b in
      let* init = match Label.Tree.add t ~key:label ~data:(`blk b) with
        | `Ok m -> Ok m
        | `Duplicate ->
          E.failf "Duplicate label for block %a" Label.pp label () in
      Blk.insns b |> E.Seq.fold ~init ~f:(fun insns i ->
          let key = Insn.label i in
          let data = `insn (i, b, Insn.lhs i) in
          match Label.Tree.add insns ~key ~data with
          | `Ok m -> Ok m
          | `Duplicate ->
            E.failf "Duplicate label for instruction %a in block %a"
              Label.pp key Label.pp label ()))

let init fn =
  let+ elts = init_elts fn in
  let cfg = Cfg.create fn in
  let pure = Var.Table.create () in
  let exp = Label.Table.create () in
  let filled = Var.Hash_set.create () in
  let func = Func.name fn in
  {func; elts; cfg; pure; exp; filled; deps = Deps.empty}

let func ctx = ctx.func

let resolve ctx l = Label.Tree.find ctx.elts l

let find_var ctx l = match resolve ctx l with
  | Some `insn (_, _, Some x) -> Ok x
  | Some _ | None -> E.failf "Missing variable for label %a" Label.pp l ()

let dependents ctx src =
  Deps.Node.succs src ctx.deps |>
  Seq.filter_map ~f:(fun dst ->
      Deps.Node.edge src dst ctx.deps |>
      Option.map ~f:(fun e -> dst, Deps.Edge.label e))

let dependencies ctx dst =
  Deps.Node.preds dst ctx.deps |>
  Seq.filter_map ~f:(fun src ->
      Deps.Node.edge src dst ctx.deps |>
      Option.map ~f:(fun e -> src, Deps.Edge.label e))

let pp_deps ppf ctx =
  Graphlib.Dot.pp_graph
    ~string_of_node:Label.to_string
    ~node_label:Label.to_string
    ~edge_label:(fun e -> Var.to_string @@ Deps.Edge.label e)
    ~nodes_of_edge:(fun e -> Deps.Edge.(src e, dst e))
    ~nodes:(Deps.nodes ctx.deps)
    ~edges:(Deps.edges ctx.deps)
    ppf

let rec pp_args args =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  (Format.pp_print_list ~pp_sep pp_pure) args

and pp_pure ppf = function
  | Palloc (l, n) ->
    Format.fprintf ppf "alloc%a(%d)" Label.pp l n
  | Pbinop (l, o, x, y) ->
    Format.fprintf ppf "%a%a(%a, %a)"
      Insn.pp_binop o Label.pp l pp_pure x pp_pure y
  | Pcall (l, _t, f, [], []) ->
    Format.fprintf ppf "%a%a()" pp_global f Label.pp l
  | Pcall (l, _t, f, args, []) ->
    Format.fprintf ppf "%a%a(%a)"
      pp_global f Label.pp l pp_args args
  | Pcall (l, _t, f, [], vargs) ->
    Format.fprintf ppf "%a%a(..., %a)"
      pp_global f Label.pp l pp_args vargs
  | Pcall (l, _t, f, args, vargs) ->
    Format.fprintf ppf "%a%a(%a, ..., %a)"
      pp_global f Label.pp l pp_args args pp_args vargs
  | Pdouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Pflag f ->
    Format.fprintf ppf "%a" Bool.pp f
  | Pint (i, t) ->
    Format.fprintf ppf "%a_%a" Bitvec.pp i Type.pp_imm t
  | Pload (l, t, a) ->
    Format.fprintf ppf "ld.%a%a(%a)"
      Type.pp_basic t Label.pp l pp_pure a
  | Psel (l, t, c, y, n) ->
    Format.fprintf ppf "sel.%a%a(%a, %a, %a)"
      Type.pp_basic t Label.pp l pp_pure c pp_pure y pp_pure n
  | Psingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Psym (s, o) ->
    if o = 0 then Format.fprintf ppf "$%s" s
    else if o < 0 then Format.fprintf ppf "$%s-%d" s (lnot o + 1)
    else Format.fprintf ppf "$%s+%d" s o
  | Punop (l, o, x) ->
    Format.fprintf ppf "%a%a(%a)"
      Insn.pp_unop o Label.pp l pp_pure x
  | Pvar v ->
    Format.fprintf ppf "%a" Var.pp v

and pp_global ppf = function
  | Gaddr a ->
    Format.fprintf ppf "%a" Bitvec.pp a
  | Gpure p ->
    Format.fprintf ppf "%a" pp_pure p
  | Gsym s ->
    Format.fprintf ppf "$%s" s

let pp_local ppf = function
  | l, [] ->
    Format.fprintf ppf "%a" Label.pp l
  | l, args ->
    Format.fprintf ppf "%a(%a)" Label.pp l pp_args args

let pp_dst ppf = function
  | Dglobal g ->
    Format.fprintf ppf "%a" pp_global g
  | Dlocal l ->
    Format.fprintf ppf "%a" pp_local l

let pp_table t tbl =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  let pp ppf (v, l) = Format.fprintf ppf "%a_%a%a"
      Bitvec.pp v Type.pp_imm t pp_local l in
  (Format.pp_print_list ~pp_sep pp) tbl

let pp ppf = function
  | Ebr (c, t, f) ->
    Format.fprintf ppf "br(%a, %a, %a)"
      pp_pure c pp_dst t pp_dst f
  | Ecall (f, [], []) ->
    Format.fprintf ppf "%a()" pp_global f
  | Ecall (f, args, []) ->
    Format.fprintf ppf "%a(%a)" pp_global f pp_args args
  | Ecall (f, [], vargs) ->
    Format.fprintf ppf "%a(..., %a)" pp_global f pp_args vargs
  | Ecall (f, args, vargs) ->
    Format.fprintf ppf "%a(%a, ..., %a)"
      pp_global f pp_args args pp_args vargs
  | Ehlt ->
    Format.fprintf ppf "hlt"
  | Ejmp d ->
    Format.fprintf ppf "jmp(%a)" pp_dst d
  | Eret (Some x) ->
    Format.fprintf ppf "ret(%a)" pp_pure x
  | Eret None ->
    Format.fprintf ppf "ret"
  | Eset (x, y) ->
    Format.fprintf ppf "%a = %a" Var.pp x pp_pure y
  | Estore (t, v, a) ->
    Format.fprintf ppf "st%a(%a, %a)"
      Type.pp_basic t pp_pure v pp_pure a
  | Esw (t, v, d, tbl) ->
    Format.fprintf ppf "sw.%a(%a, %a, [%a])"
      Type.pp_imm t pp_pure v pp_local d (pp_table t) tbl
  | Evaarg (x, t, y) ->
    Format.fprintf ppf "%a = vaarg.%a(%a)"
      Var.pp x Type.pp_basic t Var.pp y
  | Evastart x ->
    Format.fprintf ppf "vastart(%a)" Var.pp x
