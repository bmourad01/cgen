open Core
open Virtual

type prov =
  | Id of Id.t
  | Label of Label.t
[@@deriving bin_io, compare, equal, sexp]

type pure =
  | Pbinop  of prov * Insn.binop * pure * pure
  | Pbool   of bool
  | Pdouble of float
  | Pint    of Bv.t * Type.imm
  | Psel    of prov * Type.basic * pure * pure * pure
  | Psingle of Float32.t
  | Psym    of string * int
  | Punop   of prov * Insn.unop * pure
  | Pvar    of Var.t
[@@deriving bin_io, compare, equal, sexp]

and global =
  | Gaddr of Bv.t
  | Gpure of pure
  | Gsym  of string * int
[@@deriving bin_io, compare, equal, sexp]

type local = Label.t * pure list
[@@deriving bin_io, compare, equal, sexp]

type dst =
  | Dglobal of global
  | Dlocal  of local
[@@deriving bin_io, compare, equal, sexp]

type table = (Bv.t * local) list
[@@deriving bin_io, compare, equal, sexp]

type t =
  | Ebr      of pure * dst * dst
  | Ecall    of (Var.t * Type.basic) option * global * pure list * pure list
  | Ejmp     of dst
  | Eload    of Var.t * Type.basic * pure
  | Eret     of pure
  | Eset     of Var.t * pure
  | Estore   of Type.basic * pure * pure
  | Esw      of Type.imm * pure * local * table
  | Evaarg   of Var.t * Type.basic * pure
  | Evastart of pure
[@@deriving bin_io, compare, equal, sexp]

let pp_prov ppf = function
  | Id id -> Format.fprintf ppf "#%d" id
  | Label l -> Format.fprintf ppf "%a" Label.pp l

let rec pp_args args =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  (Format.pp_print_list ~pp_sep pp_pure) args

and pp_pure ppf = function
  | Pbinop (p, o, x, y) ->
    Format.fprintf ppf "%a%a(%a, %a)"
      Insn.pp_binop o pp_prov p pp_pure x pp_pure y
  | Pbool f ->
    Format.fprintf ppf "%a" Bool.pp f
  | Pdouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Pint (i, t) ->
    Format.fprintf ppf "%a_%a" Bv.pp i Type.pp_imm t
  | Psel (p, t, c, y, n) ->
    Format.fprintf ppf "sel.%a%a(%a, %a, %a)"
      Type.pp_basic t pp_prov p pp_pure c pp_pure y pp_pure n
  | Psingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Psym (s, o) ->
    if o = 0 then Format.fprintf ppf "$%s" s
    else if o < 0 then Format.fprintf ppf "$%s-%d" s (lnot o + 1)
    else Format.fprintf ppf "$%s+%d" s o
  | Punop (p, o, x) ->
    Format.fprintf ppf "%a%a(%a)"
      Insn.pp_unop o pp_prov p pp_pure x
  | Pvar v ->
    Format.fprintf ppf "%a" Var.pp v

and pp_global ppf = function
  | Gaddr a -> Format.fprintf ppf "%a" Bv.pp a
  | Gpure p -> Format.fprintf ppf "%a" pp_pure p
  | Gsym (s, 0) -> Format.fprintf ppf "$%s" s
  | Gsym (s, o) when o > 0 -> Format.fprintf ppf "$%s+%d" s o
  | Gsym (s, o) -> Format.fprintf ppf "$%s-%d" s (lnot o + 1)

let pp_local ppf = function
  | l, []   -> Format.fprintf ppf "%a" Label.pp l
  | l, args -> Format.fprintf ppf "%a(%a)" Label.pp l pp_args args

let pp_dst ppf = function
  | Dglobal g -> Format.fprintf ppf "%a" pp_global g
  | Dlocal  l -> Format.fprintf ppf "%a" pp_local l

let pp_table t tbl =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  let pp ppf (v, l) = Format.fprintf ppf "%a_%a%a"
      Bv.pp v Type.pp_imm t pp_local l in
  (Format.pp_print_list ~pp_sep pp) tbl

let pp ppf = function
  | Ebr (c, t, f) ->
    Format.fprintf ppf "br(%a, %a, %a)"
      pp_pure c pp_dst t pp_dst f
  | Ecall (_, f, [], []) ->
    Format.fprintf ppf "%a()" pp_global f
  | Ecall (_, f, args, []) ->
    Format.fprintf ppf "%a(%a)" pp_global f pp_args args
  | Ecall (_, f, [], vargs) ->
    Format.fprintf ppf "%a(..., %a)" pp_global f pp_args vargs
  | Ecall (_, f, args, vargs) ->
    Format.fprintf ppf "%a(%a, ..., %a)"
      pp_global f pp_args args pp_args vargs
  | Ejmp d ->
    Format.fprintf ppf "jmp(%a)" pp_dst d
  | Eload (x, t, a) ->
    Format.fprintf ppf "%a = ld.%a(%a)"
      Var.pp x Type.pp_basic t pp_pure a
  | Eret x ->
    Format.fprintf ppf "ret(%a)" pp_pure x
  | Eset (x, y) ->
    Format.fprintf ppf "%a = %a" Var.pp x pp_pure y
  | Estore (t, v, a) ->
    Format.fprintf ppf "st%a(%a, %a)"
      Type.pp_basic t pp_pure v pp_pure a
  | Esw (t, v, d, tbl) ->
    Format.fprintf ppf "sw.%a(%a, %a, [%a])"
      Type.pp_imm t pp_pure v pp_local d (pp_table t) tbl
  | Evaarg (x, t, a) ->
    Format.fprintf ppf "%a = vaarg.%a(%a)"
      Var.pp x Type.pp_basic t pp_pure a
  | Evastart a ->
    Format.fprintf ppf "vastart(%a)" pp_pure a
