open Core
open Virtual

module Bitvec = struct
  include Bitvec
  include Bitvec_binprot
  include Bitvec_order
  include Bitvec_sexp
end

type pure =
  | Palloc  of Label.t * int
  | Pbinop  of Label.t * Insn.binop * pure * pure
  | Pcall   of Label.t * global * pure list * pure list
  | Pdouble of float
  | Pint    of Bitvec.t * Type.imm
  | Pload   of Label.t * Type.basic * pure
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

let rec pp_args args =
  let pp_sep ppf () = Format.fprintf ppf "," in
  (Format.pp_print_list ~pp_sep pp_pure) args

and pp_pure ppf = function
  | Palloc (l, n) ->
    Format.fprintf ppf "alloc%a(%d)" Label.pp l n
  | Pbinop (l, o, x, y) ->
    Format.fprintf ppf "%a%a(%a,%a)"
      Label.pp l Insn.pp_binop o pp_pure x pp_pure y
  | Pcall (l, f, [], []) ->
    Format.fprintf ppf "%a%a()" Label.pp l pp_global f
  | Pcall (l, f, args, []) ->
    Format.fprintf ppf "%a%a(%a)"
      Label.pp l pp_global f pp_args args
  | Pcall (l, f, [], vargs) ->
    Format.fprintf ppf "%a%a(...,%a)"
      Label.pp l pp_global f pp_args vargs
  | Pcall (l, f, args, vargs) ->
    Format.fprintf ppf "%a%a(%a,...,%a)"
      Label.pp l pp_global f pp_args args pp_args vargs
  | Pdouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Pint (i, t) ->
    Format.fprintf ppf "%a_%a" Bitvec.pp i Type.pp_imm t
  | Pload (l, t, a) ->
    Format.fprintf ppf "ld.%a%a(%a)"
      Label.pp l Type.pp_basic t pp_pure a
  | Psingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Psym (s, o) ->
    if o = 0 then Format.fprintf ppf "$%s" s
    else if o < 0 then Format.fprintf ppf "$%s-%d" s (lnot o + 1) 
    else Format.fprintf ppf "$%s+%d" s o
  | Punop (l, o, x) ->
    Format.fprintf ppf "%a%a(%a)"
      Label.pp l Insn.pp_unop o pp_pure x
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

type table = (Bitvec.t * local) list
[@@deriving bin_io, compare, equal, sexp]

let pp_table tbl =
  let pp_sep ppf () = Format.fprintf ppf "," in
  let pp ppf (v, l) = Format.fprintf ppf "%a:%a" Bitvec.pp v pp_local l in
  (Format.pp_print_list ~pp_sep pp) tbl

type t =
  | Ebr    of pure * dst * dst
  | Ecall  of global * pure list * pure list
  | Ejmp   of dst
  | Eret   of pure
  | Eset   of Var.t * pure
  | Estore of Type.basic * pure * pure
  | Esw    of pure * local * table
[@@deriving bin_io, compare, equal, sexp]

let pp ppf = function
  | Ebr (c, t, f) ->
    Format.fprintf ppf "br(%a,%a,%a)"
      pp_pure c pp_dst t pp_dst f
  | Ecall (f, [], []) ->
    Format.fprintf ppf "%a()" pp_global f
  | Ecall (f, args, []) ->
    Format.fprintf ppf "%a(%a)" pp_global f pp_args args
  | Ecall (f, [], vargs) ->
    Format.fprintf ppf "%a(...,%a)" pp_global f pp_args vargs
  | Ecall (f, args, vargs) ->
    Format.fprintf ppf "%a(%a,...,%a)"
      pp_global f pp_args args pp_args vargs
  | Ejmp d ->
    Format.fprintf ppf "jmp(%a)" pp_dst d
  | Eret x ->
    Format.fprintf ppf "ret(%a)" pp_pure x
  | Eset (x, y) ->
    Format.fprintf ppf "%a = %a" Var.pp x pp_pure y
  | Estore (t, v, a) ->
    Format.fprintf ppf "st%a(%a,%a)"
      Type.pp_basic t pp_pure v pp_pure a
  | Esw (v, d, tbl) ->
    Format.fprintf ppf "sw(%a,%a,[%a])"
      pp_pure v pp_local d pp_table tbl
