open Core
open Virtual_common

module Insn = Virtual_insn

type arith_binop = Insn.arith_binop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type arith_unop = Insn.arith_unop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type bitwise_binop = Insn.bitwise_binop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type bitwise_unop = Insn.bitwise_unop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type cmp = Insn.cmp [@@deriving bin_io, compare, equal, hash, sexp_poly]
type cast = Insn.cast [@@deriving bin_io, compare, equal, hash, sexp_poly]
type copy = Insn.copy [@@deriving bin_io, compare, equal, hash, sexp_poly]
type binop = Insn.binop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type unop = Insn.unop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type basic = Insn.basic [@@deriving bin_io, compare, equal, sexp_poly]

let free_vars_of_basic = Insn.free_vars_of_basic

let pp_arith_binop = Insn.pp_arith_binop
let pp_arith_unop = Insn.pp_arith_unop
let pp_bitwise_binop = Insn.pp_bitwise_binop
let pp_bitwise_unop = Insn.pp_bitwise_unop
let pp_cmp = Insn.pp_cmp
let pp_cast = Insn.pp_cast
let pp_copy = Insn.pp_copy
let pp_binop = Insn.pp_binop
let pp_unop = Insn.pp_unop
let pp_basic = Insn.pp_basic

type mem = [
  | `load  of Var.t * Type.basic * operand
  | `store of Type.basic * operand * operand
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_mem : mem -> Var.Set.t = function
  | `load  (_, _, a) -> var_of_operand a |> var_set_of_option
  | `store (_, v, a) ->
    List.filter_map [v; a] ~f:var_of_operand |> Var.Set.of_list

let pp_mem ppf : mem -> unit = function
  | `load (x, t, a) ->
    Format.fprintf ppf "%a = ld.%a %a"
      Var.pp x Type.pp_basic t pp_operand a
  | `store (t, v, a) ->
    Format.fprintf ppf "st.%a %a, %a"
      Type.pp_basic t pp_operand v pp_operand a

type callarg = [
  | `reg of operand * string
  | `stk of operand * int
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_callarg : callarg -> Var.Set.t = function
  | `reg (o, _) | `stk (o, _) -> var_of_operand o |> var_set_of_option

let pp_callarg ppf : callarg -> unit = function
  | `reg (o, r) -> Format.fprintf ppf "%a/%s" pp_operand o r
  | `stk (o, s) -> Format.fprintf ppf "%a/+%d" pp_operand o s

type call = [
  | `call of (Var.t * Type.basic * string) list * global * callarg list
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_call : call -> Var.Set.t = function
  | `call (_, f, args) ->
    let f = var_of_global f |> var_set_of_option in
    let args =
      List.map args ~f:free_vars_of_callarg |>
      Var.Set.union_list in
    Set.union f args

let pp_call_args ppf args =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  Format.pp_print_list ~pp_sep pp_callarg ppf args

let pp_call_rets ppf rets =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  let pp_ret ppf (x, t, s) =
    Format.fprintf ppf "%a/%a/%s" Var.pp x Type.pp_basic t s in
  Format.pp_print_list ~pp_sep pp_ret ppf rets

let pp_call ppf : call -> unit = function
  | `call ([], f, args) ->
    Format.fprintf ppf "call %a(%a)"
      pp_global f pp_call_args args
  | `call (xs, f, args) ->
    Format.fprintf ppf "%a = call %a(%a)"
      pp_call_rets xs pp_global f pp_call_args args

type extra = [
  | `loadreg of Var.t * Type.basic * string
  | `storereg of string * operand
  | `setreg of string * operand
  | `stkargs of Var.t
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_extra : extra -> Var.Set.t = function
  | `loadreg _ -> Var.Set.empty
  | `storereg (_, a) | `setreg (_, a) ->
    List.filter_map [a] ~f:var_of_operand |> Var.Set.of_list
  | `stkargs x -> Var.Set.singleton x

let pp_extra ppf : extra -> unit = function
  | `loadreg (x, t, r) ->
    Format.fprintf ppf "%a = rld.%a %s" Var.pp x Type.pp_basic t r
  | `storereg (r, a) ->
    Format.fprintf ppf "st.r %s, %a" r pp_operand a
  | `setreg (r, a) ->
    Format.fprintf ppf "%s = %a" r pp_operand a
  | `stkargs x ->
    Format.fprintf ppf "%a = stkargs" Var.pp x

type op = [
  | basic
  | call
  | mem
  | extra
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_op : op -> Var.Set.t = function
  | #basic as b -> free_vars_of_basic b
  | #call  as c -> free_vars_of_call c
  | #mem   as m -> free_vars_of_mem m
  | #extra as e -> free_vars_of_extra e

let pp_op ppf : op -> unit = function
  | #basic as b -> pp_basic ppf b
  | #call  as c -> pp_call  ppf c
  | #mem   as m -> pp_mem   ppf m
  | #extra as e -> pp_extra ppf e

type t = {
  label : Label.t;
  dict  : Dict.t;
  op    : op;
} [@@deriving bin_io, compare, equal, sexp]

let create ?(dict = Dict.empty) op ~label = {label; dict; op}
let label i = i.label
let op i = i.op
let with_op i op = {i with op}
let has_label i l = Label.(i.label = l)
let map i ~f = {i with op = f i.op}
let free_vars i = free_vars_of_op i.op
let dict i = i.dict
let with_dict i dict = {i with dict}
let with_tag i tag x = {i with dict = Dict.set i.dict tag x}

let is_effectful_op : op -> bool = function
  | #call | `store _ | `storereg _ -> true
  | _ -> false

let can_store_op : op -> bool = function
  | #call | `store _ | `storereg _ -> true
  | _ -> false

let can_load_op : op -> bool = function
  | `load _ -> true
  | _ -> false

let is_effectful t = is_effectful_op t.op
let can_store t = can_store_op t.op
let can_load t = can_load_op t.op

let pp ppf d =
  Format.fprintf ppf "@[%a@ @[; %a@]@]" pp_op d.op Label.pp d.label

module Tag = struct
  let non_tail = Dict.register
      ~uuid:"3d94ecfb-36c4-4218-abc7-96c2200b4e04"
      "non-tail" (module Unit)
end

let def i = match i.op with
  | `bop (x, _, _, _)
  | `uop (x, _, _)
  | `sel (x, _, _, _, _)
  | `load (x, _, _)
  | `loadreg (x, _, _)
  | `stkargs x -> Var.Set.singleton x
  | `store _ | `storereg _ | `setreg _ -> Var.Set.empty
  | `call (xs, _, _) -> Var.Set.of_list @@ List.map xs ~f:fst3
