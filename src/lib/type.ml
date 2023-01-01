open Core
open Regular.Std

module List = struct
  include List

  let rec pp ppx sep ppf = function
    | x :: (_ :: _ as rest) ->
      Format.fprintf ppf "%a" ppx x;
      sep ppf;
      Format.fprintf ppf "%a" (pp ppx sep) rest
    | [x] -> Format.fprintf ppf "%a" ppx x
    | [] -> ()
end

type imm_base = [
  | `i32
  | `i64
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_imm_base ppf : imm_base -> unit = function
  | `i32 -> Format.fprintf ppf "w"
  | `i64 -> Format.fprintf ppf "l"

type imm = [
  | `i8
  | `i16
  | imm_base
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_imm ppf : imm -> unit = function
  | `i8  -> Format.fprintf ppf "b"
  | `i16 -> Format.fprintf ppf "h"
  | #imm_base as i -> pp_imm_base ppf i

type fp = [
  | `f32
  | `f64
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_fp ppf : fp -> unit = function
  | `f32 -> Format.fprintf ppf "s"
  | `f64 -> Format.fprintf ppf "d"

type basic = [
  | imm
  | fp
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_basic ppf : basic -> unit = function
  | #imm as i -> Format.fprintf ppf "%a" pp_imm i
  | #fp  as f -> Format.fprintf ppf "%a" pp_fp f

type field = [
  | `elt  of basic * int
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_field ppf : field -> unit = function
  | `elt (t, 1) -> Format.fprintf ppf "%a" pp_basic t
  | `elt (t, n) -> Format.fprintf ppf "%a %d" pp_basic t n
  | `name s     -> Format.fprintf ppf ":%s" s

type compound = [
  | `compound of string * int option * field list
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_compound ppf : compound -> unit = function
  | `compound (_, align, fields) ->
    let sep ppf = Format.fprintf ppf ",@;" in
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>%a@]@;}" (List.pp pp_field sep) fields

let pp_compound_decl ppf : compound -> unit = function
  | `compound (name, align, fields) ->
    let sep ppf = Format.fprintf ppf ",@;" in
    Format.fprintf ppf "type :%s = " name;
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>%a@]@;}" (List.pp pp_field sep) fields

let pp_compound_arg ppf : compound -> unit = function
  | `compound (name, _, _) -> Format.fprintf ppf ":%s" name

type special = [
  | `mem 
  | `flag
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_special ppf : special -> unit = function
  | `mem  -> Format.fprintf ppf "m"
  | `flag -> Format.fprintf ppf "f"

type arg = [
  | basic
  | compound
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_arg ppf : arg -> unit = function
  | #basic    as b -> Format.fprintf ppf "%a" pp_basic b
  | #compound as c -> Format.fprintf ppf "%a" pp_compound_arg c

module T = struct
  type t = [
    | basic
    | compound
    | special
  ] [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pp ppf : t -> unit = function
  | #basic    as b -> Format.fprintf ppf "%a" pp_basic b
  | #compound as c -> Format.fprintf ppf "%a" pp_compound c
  | #special  as s -> Format.fprintf ppf "%a" pp_special s

include Regular.Make(struct
    include T

    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Type"
  end)
