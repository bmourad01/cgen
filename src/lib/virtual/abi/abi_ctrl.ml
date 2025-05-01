open Core
open Virtual_common

module Table = Virtual_ctrl.Table

type table = Table.t [@@deriving bin_io, compare, equal, sexp]
type swindex = Virtual_ctrl.swindex [@@deriving bin_io, compare, equal, sexp_poly]

let pp_swindex = Virtual_ctrl.pp_swindex
let var_of_swindex = Virtual_ctrl.var_of_swindex

type t = [
  | `hlt
  | `jmp of dst
  | `br  of Var.t * dst * dst
  | `ret of (string * operand) list
  | `sw  of Type.imm * swindex * local * table
] [@@deriving bin_io, compare, equal, sexp]

let free_vars : t -> Var.Set.t = function
  | `hlt -> Var.Set.empty
  | `jmp d -> free_vars_of_dst d
  | `br (x, y, n) ->
    Var.Set.union_list [
      Var.Set.singleton x;
      free_vars_of_dst y;
      free_vars_of_dst n;
    ]
  | `ret xs ->
    List.filter_map xs
      ~f:(Fn.compose var_of_operand snd) |>
    Var.Set.of_list
  | `sw (_, x, d, tbl) ->
    Var.Set.union_list [
      var_set_of_option @@ var_of_swindex x;
      free_vars_of_local d;
      Table.free_vars tbl;
    ]

let pp ppf : t -> unit = function
  | `hlt -> Format.fprintf ppf "hlt"
  | `jmp d ->
    Format.fprintf ppf "jmp %a" pp_dst d
  | `br (c, t, f) ->
    Format.fprintf ppf "br %a, %a, %a" Var.pp c pp_dst t pp_dst f
  | `ret [] ->
    Format.fprintf ppf "ret"
  | `ret xs ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    let pp_ret ppf (r, o) = Format.fprintf ppf "%s/%a" r pp_operand o in
    Format.fprintf ppf "ret %a"
      (Format.pp_print_list ~pp_sep pp_ret) xs
  | `sw (t, x, ld, tbl) ->
    Format.fprintf ppf "switch.%a %a, %a [@[<v 0>%a@]]"
      Type.pp_imm t pp_swindex x pp_local ld Table.pp tbl
