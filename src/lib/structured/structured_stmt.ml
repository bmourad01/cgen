open Core

type cond = [
  | `var of Var.t
  | `cmp of Virtual.Insn.cmp * Virtual.operand * Virtual.operand
] [@@deriving bin_io, compare, equal, sexp]

type t = [
  | Virtual.Insn.op
  | `nop
  | `seq of t * t
  | `ite of cond * t * t
  | `when_ of cond * t
  | `unless of cond * t
  | `loop of t
  | `while_ of cond * t
  | `dowhile of t * cond
  | `break
  | `continue
  | `sw of Var.t * Type.imm * swcase list
  | `label of Label.t * Var.t list * t
  | `goto of Virtual.dst
  | `hlt
  | `ret of Virtual.operand option
] [@@deriving bin_io, compare, equal, sexp]

and swcase = [
  | `case of Bv.t * t
  | `default of t
] [@@deriving bin_io, compare, equal, sexp]

let pp_cond ppf : cond -> unit = function
  | `var v ->
    Format.fprintf ppf "%a" Var.pp v
  | `cmp (k, l, r) ->
    Format.fprintf ppf "%a %a, %a"
      Virtual.Insn.pp_cmp k
      Virtual.pp_operand l
      Virtual.pp_operand r

let rec pp ppf : t -> unit = function
  | #Virtual.Insn.op as op ->
    Format.fprintf ppf "%a" Virtual.Insn.pp_op op
  |`nop ->
    Format.fprintf ppf "nop"
  | `seq (t1, t2) ->
    Format.fprintf ppf "%a;@;%a" pp t1 pp t2
  | `ite (c, y, n) ->
    Format.fprintf ppf "if %a {@;@[<v 2>  %a@]@;} else {@;@[<v 2>  %a@]@;}"
      pp_cond c pp y pp n
  | `when_ (c, b) ->
    Format.fprintf ppf "when %a [@;@[<v 2>  %a@]@;}" pp_cond c pp b
  | `unless (c, b) ->
    Format.fprintf ppf "unless %a [@;@[<v 2>  %a@]@;}" pp_cond c pp b
  | `loop b ->
    Format.fprintf ppf "loop {@;@[<v 2>  %a@]@;}" pp b
  | `while_ (c, b) ->
    Format.fprintf ppf "while %a {@;@[<v 2>  %a@]@;}"
      pp_cond c pp b
  | `dowhile (b, c) ->
    Format.fprintf ppf "do {@;@[<v 2>  %a@]@;} while %a"
      pp b pp_cond c
  | `break ->
    Format.fprintf ppf "break"
  | `continue ->
    Format.fprintf ppf "continue"
  | `sw (i, ty, cs) ->
    let pp_sep ppf () = Format.fprintf ppf "@;" in
    Format.fprintf ppf "switch.%a %a {@;@[<v 0>%a@]@;}"
      Var.pp i Type.pp_imm ty
      (Format.pp_print_list ~pp_sep (pp_swcase ty))
      cs
  | `label (l, [], b) ->
    Format.fprintf ppf "@[<v 0>%a:@;@[<v 2>  %a@]@]" Label.pp l pp b
  | `label (l, args, b) ->
    Format.fprintf ppf "@[<v 0>%a(%a):@;@[<v 2>  %a@]@]" Label.pp l
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
         Var.pp) args pp b
  | `goto l ->
    Format.fprintf ppf "goto %a" Virtual.pp_dst l
  | `hlt ->
    Format.fprintf ppf "hlt"
  | `ret None ->
    Format.fprintf ppf "ret"
  | `ret Some x ->
    Format.fprintf ppf "ret %a" Virtual.pp_operand x

and pp_swcase ty ppf : swcase -> unit = function
  | `case (i, b) ->
    Format.fprintf ppf "case %a_%a:@;@[<v 2>  %a@]"
      Bv.pp i Type.pp_imm ty pp b
  | `default d ->
    Format.fprintf ppf "default:@;@[<v 2>  %a@]" pp d
