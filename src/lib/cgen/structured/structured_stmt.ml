open Core

module Bv = Cgen_utils.Bv

type goto = [
  | Virtual.global
  | `label of Label.t
] [@@deriving bin_io, compare, equal, sexp]

let pp_goto ppf : goto -> unit = function
  | #Virtual.global as g ->
    Format.fprintf ppf "%a" Virtual.pp_global g
  | `label l ->
    Format.fprintf ppf "%a" Label.pp l

type cond = [
  | `var of Var.t
  | `cmp of Virtual.Insn.cmp * Virtual.operand * Virtual.operand
] [@@deriving bin_io, compare, equal, sexp]

let pp_cond ppf : cond -> unit = function
  | `var v ->
    Format.fprintf ppf "%a" Var.pp v
  | `cmp (k, l, r) ->
    Format.fprintf ppf "%a %a, %a"
      Virtual.Insn.pp_cmp k
      Virtual.pp_operand l
      Virtual.pp_operand r

type t = [
  | Virtual.Insn.op
  | `nop
  | `seq of t * t
  | `ite of cond * t * t
  | `loop of t * t
  | `break
  | `continue
  | `sw of Virtual.Ctrl.swindex * Type.imm * swcase list
  | `label of Label.t * t
  | `goto of goto
  | `hlt
  | `ret of Virtual.operand option
] [@@deriving bin_io, compare, equal, sexp]

and swcase = [
  | `case of Bv.t * t
  | `default of t
] [@@deriving bin_io, compare, equal, sexp]

let rec pp ppf : t -> unit = function
  | #Virtual.Insn.op as op ->
    Virtual.Insn.pp_op ppf op
  |`nop ->
    Format.fprintf ppf "nop"
  | `seq (t1, t2) ->
    Format.fprintf ppf "%a;@;%a" pp t1 pp t2
  | `ite (c, y, n) -> pp_ite ppf c y n
  | `loop (b, s) -> pp_loop ppf b s
  | `break ->
    Format.fprintf ppf "break"
  | `continue ->
    Format.fprintf ppf "continue"
  | `sw (i, ty, cs) ->
    let pp_sep ppf () = Format.fprintf ppf "@;" in
    Format.fprintf ppf
      "switch.%a %a {@;@[<v 0>%a@]@;}"
      Type.pp_imm ty Virtual.Ctrl.pp_swindex i
      (Format.pp_print_list ~pp_sep (pp_swcase ty))
      cs
  | `label (l, b) ->
    Format.fprintf ppf
      "@[<v 0>%a:@;@[<v 2>  %a@]@]"
      Label.pp l pp b
  | `goto g ->
    Format.fprintf ppf "goto %a" pp_goto g
  | `hlt ->
    Format.fprintf ppf "hlt"
  | `ret None ->
    Format.fprintf ppf "ret"
  | `ret Some x ->
    Format.fprintf ppf "ret %a" Virtual.pp_operand x

and pp_swcase ty ppf : swcase -> unit = function
  | `case (i, b) ->
    Format.fprintf ppf
      "case %a_%a:@;@[<v 2>  %a@]"
      Bv.pp i Type.pp_imm ty pp b
  | `default d ->
    Format.fprintf ppf "default:@;@[<v 2>  %a@]" pp d

and pp_while ppf c b =
  Format.fprintf ppf
    "while %a {@;@[<v 2>  %a@]@;}"
    pp_cond c pp b

and pp_dowhile ppf b c =
  Format.fprintf ppf
    "do {@;@[<v 2>  %a@]@;} while %a"
    pp b pp_cond c

and pp_loop ppf body step = match body, step with
  (* A `while` loop tests at the top of the body, with no step region. *)
  | (`seq (`ite (c, `nop, `break), b) | `ite (c, b, `break)), `nop ->
    pp_while ppf c b
  | `ite (`cmp (k, l, r), `break, b), `nop ->
    let k = Virtual.Insn.negate_cmp k in
    pp_while ppf (`cmp (k, l, r)) b
  (* A `do`-`while` loop's step region is the condition test. *)
  | b, `ite (c, `nop, `break) -> pp_dowhile ppf b c
  | b, `ite (`cmp (k, l, r), `break, `nop) ->
    let k = Virtual.Insn.negate_cmp k in
    pp_dowhile ppf b (`cmp (k, l, r))
  (* A plain loop with no step region. *)
  | b, `nop ->
    Format.fprintf ppf "loop {@;@[<v 2>  %a@]@;}" pp b
  (* The general case: a loop with an explicit step region (e.g. a
     `for` loop's increment). *)
  | b, s ->
    Format.fprintf ppf
      "loop {@;@[<v 2>  %a@]@;} step {@;@[<v 2>  %a@]@;}"
      pp b pp s

and pp_when ppf c b =
  Format.fprintf ppf
    "when %a {@;@[<v 2>  %a@]@;}"
    pp_cond c pp b

and pp_unless ppf c b =
  Format.fprintf ppf
    "unless %a {@;@[<v 2>  %a@]@;}"
    pp_cond c pp b

and pp_ite ppf c y n = match y, n with
  | `nop, _ -> pp_unless ppf c n
  | _, `nop -> pp_when ppf c y
  | _ ->
    Format.fprintf ppf
      "if %a {@;@[<v 2>  %a@]@;} else {@;@[<v 2>  %a@]@;}"
      pp_cond c pp y pp n

let when_ c b = `ite (c, b, `nop)
let unless c b = `ite (c, `nop, b)

let while_ c b =
  `loop (
    `seq (
      unless c `break,
      b
    ),
    `nop
  )

let dowhile b c =
  `loop (
    b,
    unless c `break
  )

let[@tail_mod_cons] rec seq : t list -> t = function
  | [] -> `nop
  | [s] -> s
  | s :: ss -> `seq (s, seq ss)

let[@tail_mod_cons] rec normalize (s : t) : t = match s with
  (* Leaf case: nothing to do here. *)
  | #Virtual.Insn.op
  | `nop
  | `break
  | `continue
  | `hlt
  | `goto _
  | `ret _
    -> s
  (* Useless nop. *)
  | `seq (`nop, s)
  | `seq (s, `nop)
    -> normalize s
  (* Associate sequences to the right. *)
  | `seq (`seq (s1, s2), s3) ->
    normalize @@ `seq (s1, `seq (s2, s3))
  (* The rest of these are just boring tree traversals. *)
  | `seq (s1, s2) ->
    begin match normalize s1, normalize s2 with
      | `nop, s -> s
      | s, `nop -> s
      | s1, s2 -> `seq (s1, s2)
    end
  | `ite (c, y, n) ->
    `ite (c, (normalize [@tailcall false]) y, (normalize [@tailcall]) n)
  | `loop (b, s) ->
    `loop ((normalize [@tailcall false]) b, (normalize [@tailcall]) s)
  | `sw (i, ty, cs) ->
    `sw (i, ty, List.map cs ~f:normalize_swcase)
  | `label (l, b) -> `label (l, normalize b)

and normalize_swcase : swcase -> swcase = function
  | `case (v, c) -> `case (v, normalize c)
  | `default d -> `default (normalize d)
