open Core
open Regular.Std

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
  | `i8 -> Format.fprintf ppf "b"
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
  | #fp as f -> Format.fprintf ppf "%a" pp_fp f

type alignment = [
  | `default
  | `align of int
] [@@deriving bin_io, compare, equal, hash, sexp]

type field = [
  | basic
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_field ppf : field -> unit = function
  | #basic as b -> Format.fprintf ppf "%a" pp_basic b
  | `name s -> Format.fprintf ppf ":%s" s

type compound = [
  | `compound of string * alignment * field list
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_compound ppf : compound -> unit = function
  | `compound (name, align, fields) ->
    let rec pp_fields ppf = function
      | f :: (_ :: _ as rest) ->
        Format.fprintf ppf "%a, %a" pp_field f pp_fields rest
      | [f] -> Format.fprintf ppf "%a" pp_field f
      | [] -> () in
    Format.fprintf ppf "struct :%s " name;
    begin match align with
      | `default -> ()
      | `align n -> Format.fprintf ppf "align %d " n
    end;
    Format.fprintf ppf "{%a}" pp_fields fields

type special = [
  | `mem 
  | `flag
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_special ppf : special -> unit = function
  | `mem -> Format.fprintf ppf "m"
  | `flag -> Format.fprintf ppf "f"

module T = struct
  type t = [
    | basic
    | compound
    | special
  ] [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let rec pp ppf : t -> unit = function
  | #basic as b -> Format.fprintf ppf "%a" pp_basic b
  | #compound as c -> Format.fprintf ppf "%a" pp_compound c
  | #special as s -> Format.fprintf ppf "%a" pp_special s

include Regular.Make(struct
    include T

    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Type"
  end)
