open Core
open Regular.Std
open Common

type arith_binop = [
  | `add  of Type.basic
  | `div  of Type.basic
  | `mul  of Type.basic
  | `mulh of Type.imm
  | `rem  of Type.basic
  | `sub  of Type.basic
  | `udiv of Type.imm
  | `urem of Type.imm
] [@@deriving bin_io, compare, equal, sexp]

let pp_arith_binop ppf : arith_binop -> unit = function
  | `add  t -> Format.fprintf ppf "add.%a"  Type.pp_basic t
  | `div  t -> Format.fprintf ppf "div.%a"  Type.pp_basic t
  | `mul  t -> Format.fprintf ppf "mul.%a"  Type.pp_basic t
  | `mulh t -> Format.fprintf ppf "mulh.%a" Type.pp_imm t
  | `rem  t -> Format.fprintf ppf "rem.%a"  Type.pp_basic t
  | `sub  t -> Format.fprintf ppf "sub.%a"  Type.pp_basic t
  | `udiv t -> Format.fprintf ppf "udiv.%a" Type.pp_imm t
  | `urem t -> Format.fprintf ppf "urem.%a" Type.pp_imm t

type arith_unop = [
  | `neg of Type.basic
] [@@deriving bin_io, compare, equal, sexp]

let pp_arith_unop ppf : arith_unop -> unit = function
  | `neg t -> Format.fprintf ppf "neg.%a" Type.pp_basic t

type bitwise_binop = [
  | `and_ of Type.imm
  | `or_  of Type.imm
  | `asr_ of Type.imm
  | `lsl_ of Type.imm
  | `lsr_ of Type.imm
  | `rol  of Type.imm
  | `ror  of Type.imm
  | `xor  of Type.imm
] [@@deriving bin_io, compare, equal, sexp]

let pp_bitwise_binop ppf : bitwise_binop -> unit = function
  | `and_ t -> Format.fprintf ppf "and.%a" Type.pp_imm t
  | `or_  t -> Format.fprintf ppf  "or.%a" Type.pp_imm t
  | `asr_ t -> Format.fprintf ppf "asr.%a" Type.pp_imm t
  | `lsl_ t -> Format.fprintf ppf "lsl.%a" Type.pp_imm t
  | `lsr_ t -> Format.fprintf ppf "lsr.%a" Type.pp_imm t
  | `rol  t -> Format.fprintf ppf "rol.%a" Type.pp_imm t
  | `ror  t -> Format.fprintf ppf "ror.%a" Type.pp_imm t
  | `xor  t -> Format.fprintf ppf "xor.%a" Type.pp_imm t

type bitwise_unop = [
  | `not_ of Type.imm
] [@@deriving bin_io, compare, equal, sexp]

let pp_bitwise_unop ppf : bitwise_unop -> unit = function
  | `not_ t -> Format.fprintf ppf "not.%a" Type.pp_imm t

type mem = [
  | `alloc of int
  | `load  of Type.basic * Var.t * operand
  | `store of Type.basic * Var.t * operand * operand
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_mem : mem -> Var.Set.t = function
  | `load  (_, x, a) ->
    var_of_operand a |> Option.to_list |> List.cons x |> Var.Set.of_list
  | `store (_, x, a, v) ->
    List.filter_map [a; v] ~f:var_of_operand |> List.cons x |> Var.Set.of_list
  | `alloc _ -> Var.Set.empty

let pp_mem ppf : mem -> unit = function
  | `alloc n ->
    Format.fprintf ppf "alloc %d" n
  | `load (t, m, a) ->
    Format.fprintf ppf "ld.%a %a[%a]" Type.pp_basic t Var.pp m pp_operand a
  | `store (t, m, a, x) ->
    Format.fprintf ppf "st.%a %a[%a], %a"
      Type.pp_basic t Var.pp m pp_operand a pp_operand x

type cmp = [
  | `eq  of Type.basic
  | `ge  of Type.basic
  | `gt  of Type.basic
  | `le  of Type.basic
  | `lt  of Type.basic
  | `ne  of Type.basic
  | `o   of Type.fp
  | `sge of Type.imm
  | `sgt of Type.imm
  | `sle of Type.imm
  | `slt of Type.imm
  | `uo  of Type.fp
] [@@deriving bin_io, compare, equal, sexp]

let pp_cmp ppf : cmp -> unit = function
  | `eq  t -> Format.fprintf ppf "eq.%a"  Type.pp_basic t
  | `ge  t -> Format.fprintf ppf "ge.%a"  Type.pp_basic t
  | `gt  t -> Format.fprintf ppf "gt.%a"  Type.pp_basic t
  | `le  t -> Format.fprintf ppf "le.%a"  Type.pp_basic t
  | `lt  t -> Format.fprintf ppf "lt.%a"  Type.pp_basic t
  | `ne  t -> Format.fprintf ppf "ne.%a"  Type.pp_basic t
  | `o   t -> Format.fprintf ppf "o.%a"   Type.pp_fp    t
  | `sge t -> Format.fprintf ppf "sge.%a" Type.pp_imm   t
  | `sgt t -> Format.fprintf ppf "sgt.%a" Type.pp_imm   t
  | `sle t -> Format.fprintf ppf "sle.%a" Type.pp_imm   t
  | `slt t -> Format.fprintf ppf "slt.%a" Type.pp_imm   t
  | `uo  t -> Format.fprintf ppf "uo.%a"  Type.pp_fp    t

type cast = [
  | `bits   of Type.basic
  | `fext   of Type.fp
  | `ftosi  of Type.fp * Type.imm
  | `ftoui  of Type.fp * Type.imm
  | `ftrunc of Type.fp
  | `itrunc of Type.imm
  | `sext   of Type.imm
  | `sitof  of Type.imm * Type.fp
  | `uitof  of Type.imm * Type.fp
  | `zext   of Type.imm
] [@@deriving bin_io, compare, equal, sexp]

let pp_cast ppf : cast -> unit = function
  | `bits t ->
    Format.fprintf ppf "bits.%a" Type.pp_basic t
  | `fext t ->
    Format.fprintf ppf "fext.%a" Type.pp_fp t
  | `ftosi (tf, ti) ->
    Format.fprintf ppf "ftosi.%a.%a" Type.pp_fp tf Type.pp_imm ti
  | `ftoui (tf, ti) ->
    Format.fprintf ppf "ftoui.%a.%a" Type.pp_fp tf Type.pp_imm ti
  | `ftrunc t ->
    Format.fprintf ppf "ftrunc.%a" Type.pp_fp t
  | `itrunc t ->
    Format.fprintf ppf "itrunc.%a" Type.pp_imm t
  | `sext t ->
    Format.fprintf ppf "sext.%a" Type.pp_imm t
  | `sitof (ti, tf) ->
    Format.fprintf ppf "sitof.%a.%a" Type.pp_imm ti Type.pp_fp tf
  | `uitof (ti, tf) ->
    Format.fprintf ppf "uitof.%a.%a" Type.pp_imm ti Type.pp_fp tf
  | `zext t ->
    Format.fprintf ppf "zext.%a" Type.pp_imm t

type copy = [
  | `copy of Type.basic
] [@@deriving bin_io, compare, equal, sexp]

let pp_copy ppf : copy -> unit = function
  | `copy t -> Format.fprintf ppf "copy.%a" Type.pp_basic t

type binop = [
  | arith_binop
  | bitwise_binop
  | cmp
] [@@deriving bin_io, compare, equal, sexp]

let pp_binop ppf : binop -> unit = function
  | #arith_binop as a -> Format.fprintf ppf "%a" pp_arith_binop a
  | #bitwise_binop as b -> Format.fprintf ppf "%a" pp_bitwise_binop b
  | #cmp as c -> Format.fprintf ppf "%a" pp_cmp c

type unop = [
  | arith_unop
  | bitwise_unop
  | cast
  | copy
] [@@deriving bin_io, compare, equal, sexp]

let pp_unop ppf : unop -> unit = function
  | #arith_unop as a -> Format.fprintf ppf "%a" pp_arith_unop a
  | #bitwise_unop as b -> Format.fprintf ppf "%a" pp_bitwise_unop b
  | #cast as c -> Format.fprintf ppf "%a" pp_cast c
  | #copy as c -> Format.fprintf ppf "%a" pp_copy c

type basic = [
  | `bop of Var.t * binop * operand * operand
  | `uop of Var.t * unop  * operand
  | `mem of Var.t * mem
  | `sel of Var.t * Type.basic * Var.t * operand * operand
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_basic : basic -> Var.Set.t = function
  | `bop (_, _, l, r) ->
    List.filter_map [l; r] ~f:var_of_operand |> Var.Set.of_list
  | `uop (_, _, a) -> var_set_of_option @@ var_of_operand a
  | `mem (_, m) -> free_vars_of_mem m
  | `sel (_, _, x, t, f) ->
    List.filter_map [t; f] ~f:var_of_operand |> List.cons x |> Var.Set.of_list

let pp_basic ppf : basic -> unit = function
  | `bop (x, b, l, r) ->
    Format.fprintf ppf "%a = %a %a, %a"  Var.pp x pp_binop b pp_operand l pp_operand r
  | `uop (x, u, a) ->
    Format.fprintf ppf "%a = %a %a" Var.pp x pp_unop u pp_operand a
  | `mem (x, m) ->
    Format.fprintf ppf "%a = %a" Var.pp x pp_mem m
  | `sel (x, t, c, l, r) ->
    Format.fprintf ppf "%a = sel.%a %a, %a, %a"
      Var.pp x Type.pp_basic t Var.pp c pp_operand l pp_operand r

type call = [
  | `call of (Var.t * Type.basic) option * global * operand list * operand list
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_call : call -> Var.Set.t = function
  | `call (_, f, args, vargs) ->
    let f = var_of_global f |> Option.to_list |> Var.Set.of_list in
    let args = List.filter_map args ~f:var_of_operand |> Var.Set.of_list in
    let vargs = List.filter_map vargs ~f:var_of_operand |> Var.Set.of_list in
    Var.Set.union_list [f; args; vargs]

let is_variadic : call -> bool = function
  | `call (_, _, _, vargs) -> not @@ List.is_empty vargs

let pp_call_args ppf args =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  Format.pp_print_list ~pp_sep pp_operand ppf args

let pp_call_vargs args ppf = function
  | [] -> ()
  | vargs ->
    if not (List.is_empty args) then Format.fprintf ppf ", ";
    Format.fprintf ppf "..., %a" pp_call_args vargs

let pp_call_res ppf = function
  | None -> Format.fprintf ppf "call "
  | Some (x, t) ->
    Format.fprintf ppf "%a = call.%a " Var.pp x Type.pp_basic t

let pp_call ppf c =
  let res, dst, args, vargs = match c with
    | `call (Some (v, t), d, a, va) -> Some (v, t), d, a, va
    | `call (None, d, a, va) -> None, d, a, va in
  Format.fprintf ppf "%a%a(%a%a)"
    pp_call_res res
    pp_global dst
    pp_call_args args
    (pp_call_vargs args) vargs

type variadic = [
  | `vastart of Var.t
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_variadic : variadic -> Var.Set.t = function
  | `vastart x -> Var.Set.singleton x

let pp_variadic ppf : variadic -> unit = function
  | `vastart x -> Format.fprintf ppf "vastart %a" Var.pp x

type op = [
  | basic
  | call
  | variadic
] [@@deriving bin_io, compare, equal, sexp]

let lhs_of_op : op -> Var.t option = function
  | `bop     (x, _, _, _)
  | `uop     (x, _, _)
  | `mem     (x, _)
  | `sel     (x, _, _, _, _)
  | `call    (Some (x, _), _, _, _) -> Some x
  | `call    _ -> None
  | `vastart _ -> None

let op_has_lhs d v = match lhs_of_op d with
  | Some x -> Var.(x = v)
  | None -> false

let free_vars_of_op : op -> Var.Set.t = function
  | #basic    as b -> free_vars_of_basic b
  | #call     as c -> free_vars_of_call c
  | #variadic as v -> free_vars_of_variadic v

let pp_op ppf : op -> unit = function
  | #basic    as b -> pp_basic    ppf b
  | #call     as c -> pp_call     ppf c
  | #variadic as v -> pp_variadic ppf v

type t = {
  label : Label.t;
  op    : op;
} [@@deriving bin_io, compare, equal, sexp]

let create op ~label = {label; op}
let label d = d.label
let op d = d.op
let has_label d l = Label.(d.label = l)
let map d ~f = {d with op = f d.op}
let lhs d = lhs_of_op d.op
let has_lhs d v = op_has_lhs d.op v
let free_vars d = free_vars_of_op d.op

let pp ppf d =
  Format.fprintf ppf "@[%a@ @[; %a@]@]" pp_op d.op Label.pp d.label
