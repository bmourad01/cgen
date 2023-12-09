open Core
open Abi_common

type arith_binop = Insn.arith_binop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type arith_unop = Insn.arith_unop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type bitwise_binop = Insn.bitwise_binop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type bitwise_unop = Insn.bitwise_unop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type cmp = Insn.cmp [@@deriving bin_io, compare, equal, hash, sexp_poly]
type cast = Insn.cast [@@deriving bin_io, compare, equal, hash, sexp_poly]
type copy = Insn.copy [@@deriving bin_io, compare, equal, hash, sexp_poly]
type binop = Insn.binop [@@deriving bin_io, compare, equal, hash, sexp_poly]
type unop = Insn.unop [@@deriving bin_io, compare, equal, hash, sexp_poly]

let pp_arith_binop = Insn.pp_arith_binop
let pp_arith_unop = Insn.pp_arith_unop
let pp_bitwise_binop = Insn.pp_bitwise_binop
let pp_bitwise_unop = Insn.pp_bitwise_unop
let pp_cmp = Insn.pp_cmp
let pp_cast = Insn.pp_cast
let pp_copy = Insn.pp_copy
let pp_binop = Insn.pp_binop
let pp_unop = Insn.pp_unop

type basic = [
  | `bop of var * binop * operand * operand
  | `uop of var * unop * operand
  | `sel of var * Type.basic * var * operand * operand
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_basic : basic -> (var, var_comparator) Set.t = function
  | `bop (_, _, l, r) ->
    List.filter_map [l; r] ~f:var_of_operand |>
    Set.of_list (module Var_comparator)
  | `uop (_, _, a) -> var_set_of_option @@ var_of_operand a
  | `sel (_, _, c, l, r) ->
    List.filter_map [l; r] ~f:var_of_operand |>
    List.cons c |> Set.of_list (module Var_comparator)

let pp_basic ppf : basic -> unit = function
  | `bop (x, b, l, r) ->
    Format.fprintf ppf "%a = %a %a, %a"
      pp_var x pp_binop b pp_operand l pp_operand r
  | `uop (x, u, a) ->
    Format.fprintf ppf "%a = %a %a"
      pp_var x pp_unop u pp_operand a
  | `sel (x, t, c, l, r) ->
    Format.fprintf ppf "%a = sel.%a %a, %a, %a"
      pp_var x Type.pp_basic t pp_var c pp_operand l pp_operand r

type call = [
  | `call of string list * global * operand list
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_call : call -> (var, var_comparator) Set.t = function
  | `call (_, f, args) ->
    let f = var_of_global f |> var_set_of_option in
    let args =
      List.filter_map args ~f:var_of_operand |>
      Set.of_list (module Var_comparator) in
    Set.union f args

let pp_call_args ppf args =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  Format.pp_print_list ~pp_sep pp_operand ppf args

let pp_call_rets ppf rets =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  let pp_ret ppf s = Format.fprintf ppf "%s" s in
  Format.pp_print_list ~pp_sep pp_ret ppf rets

let pp_call ppf : call -> unit = function
  | `call ([], f, args) ->
    Format.fprintf ppf "call %a(%a)"
      pp_global f pp_call_args args
  | `call (xs, f, args) ->
    Format.fprintf ppf "%a = call %a(%a)"
      pp_call_rets xs pp_global f pp_call_args args

type mem = [
  | `load  of var * Type.basic * operand
  | `store of Type.basic * operand * operand
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_mem : mem -> (var, var_comparator) Set.t = function
  | `load  (_, _, a) -> var_of_operand a |> var_set_of_option
  | `store (_, v, a) ->
    List.filter_map [v; a] ~f:var_of_operand |>
    Set.of_list (module Var_comparator)

let pp_mem ppf : mem -> unit = function
  | `load (x, t, a) ->
    Format.fprintf ppf "%a = ld.%a %a"
      pp_var x Type.pp_basic t pp_operand a
  | `store (t, v, a) ->
    Format.fprintf ppf "st.%a %a, %a"
      Type.pp_basic t pp_operand v pp_operand a

type memv = [
  | `storev of string * operand
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_memv : memv -> (var, var_comparator) Set.t = function
  | `storev (v, a) ->
    List.filter_map [a] ~f:var_of_operand |>
    List.cons (`reg v) |>
    Set.of_list (module Var_comparator)

let pp_memv ppf : memv -> unit = function
  | `storev (v, a) ->
    Format.fprintf ppf "st.v %s, %a" v pp_operand a

type op = [
  | basic
  | call
  | mem
  | memv
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_op : op -> (var, var_comparator) Set.t = function
  | #basic as b -> free_vars_of_basic b
  | #call  as c -> free_vars_of_call c
  | #mem   as m -> free_vars_of_mem m
  | #memv  as m -> free_vars_of_memv m

let pp_op ppf : op -> unit = function
  | #basic as b -> pp_basic ppf b
  | #call  as c -> pp_call  ppf c
  | #mem   as m -> pp_mem   ppf m
  | #memv  as m -> pp_memv  ppf m

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
  | #call | `store _ | `storev _ -> true
  | _ -> false

let can_store_op : op -> bool = function
  | #call | `store _ | `storev _ -> true
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
