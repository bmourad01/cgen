open Core
open Common

type var = [
  | `var of Var.t
  | `reg of string
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_var ppf : var -> unit = function
  | `var x -> Format.fprintf ppf "%a" Var.pp x
  | `reg s -> Format.fprintf ppf "%s" s

module Var_comparator = struct
  type t = var

  include Comparator.Make(struct
      type t = var [@@deriving compare, sexp]
    end)
end

type var_comparator = Var_comparator.comparator_witness

type operand = [
  | const
  | var
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_operand ppf : operand -> unit = function
  | #const as c -> Format.fprintf ppf "%a" pp_const c
  | #var as v -> Format.fprintf ppf "%a" pp_var v

let var_of_operand = function
  | #var as v -> Some v
  | _ -> None

let var_set_of_option x =
  Option.to_list x |> Set.of_list (module Var_comparator)

type global = [
  | `addr of Bv.t
  | `sym  of string * int
  | `var  of var
] [@@deriving bin_io, compare, equal, sexp]

let var_of_global : global -> var option = function
  | `var x -> Some x
  | `addr _ | `sym _ -> None

let pp_global ppf : global -> unit = function
  | `addr a -> Format.fprintf ppf "%a" Bv.pp a
  | `sym (s, 0) -> Format.fprintf ppf "$%s" s
  | `sym (s, o) when o > 0 -> Format.fprintf ppf "$%s+%d" s o
  | `sym (s, o) -> Format.fprintf ppf "$%s-%d" s (lnot o + 1)
  | `var v -> Format.fprintf ppf "%a" pp_var v

type local = [
  | `label of Label.t * operand list
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_local : local -> (var, var_comparator) Set.t = function
  | `label (_, args) ->
    let init = Set.empty (module Var_comparator) in
    List.fold args ~init ~f:(fun s -> function
        | #var as v -> Set.add s v
        | _ -> s)

let pp_local ppf : local -> unit = function
  | `label (l, []) -> Format.fprintf ppf "%a" Label.pp l
  | `label (l, args) ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    Format.fprintf ppf "%a(%a)"
      Label.pp l (Format.pp_print_list ~pp_sep pp_operand) args

type dst = [
  | global
  | local
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_dst : dst -> (var, var_comparator) Set.t = function
  | `var x -> Set.singleton (module Var_comparator) x
  | #local as l -> free_vars_of_local l
  | _ -> Set.empty (module Var_comparator)

let pp_dst ppf : dst -> unit = function
  | #global as g -> Format.fprintf ppf "%a" pp_global g
  | #local  as l -> Format.fprintf ppf "%a" pp_local l
