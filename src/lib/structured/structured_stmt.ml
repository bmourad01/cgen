open Core

type t = [
  | Virtual.Insn.op
  | `nop
  | `seq of t * t
  | `ite of Var.t * t * t
  | `while_ of Var.t * t
  | `dowhile of t * Var.t
  | `sw of Var.t * Type.imm * (Bv.t * t) list
  | `label of Label.t
  | `goto of Label.t
  | `hlt
  | `ret of Virtual.operand option
] [@@deriving bin_io, compare, equal, sexp]

let rec pp ppf : t -> unit = function
  | #Virtual.Insn.op as op ->
    Format.fprintf ppf "%a" Virtual.Insn.pp_op op
  |`nop ->
    Format.fprintf ppf "nop"
  | `seq (t1, t2) ->
    Format.fprintf ppf "%a;@;%a" pp t1 pp t2
  | `ite (c, y, n) ->
    Format.fprintf ppf "if %a {@;@[<v 2>  %a@]@;} else {@;@[<v 2>  %a@]@;}"
      Var.pp c pp y pp n
  | `while_ (c, b) ->
    Format.fprintf ppf "while %a {@;@[<v 2>  %a@]}"
      Var.pp c pp b
  | `dowhile (b, c) ->
    Format.fprintf ppf "do {@;@[<v 2>  %a@]@;} while %a"
      pp b Var.pp c
  | `sw (i, ty, cs) ->
    let pp_sep ppf () = Format.fprintf ppf "@;" in
    let pp_case ppf (l, s) =
      Format.fprintf ppf "case %a:@;@[<v 2>  %a@]"
        Bv.pp l pp s in
    Format.fprintf ppf "switch.%a %a {@;@[<v 0>%a@]}"
      Var.pp i Type.pp_imm ty
      (Format.pp_print_list ~pp_sep pp_case)
      cs
  | `label l ->
    Format.fprintf ppf "%a:" Label.pp l
  | `goto l ->
    Format.fprintf ppf "goto %a" Label.pp l
  | `hlt ->
    Format.fprintf ppf "hlt"
  | `ret None ->
    Format.fprintf ppf "ret"
  | `ret Some x ->
    Format.fprintf ppf "ret %a" Virtual.pp_operand x
