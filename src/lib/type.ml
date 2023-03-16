open Core
open Regular.Std

type imm_base = [
  | `i32
  | `i64
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_imm_base : imm_base -> int = function
  | `i32 -> 32
  | `i64 -> 64

let pp_imm_base ppf : imm_base -> unit = function
  | `i32 -> Format.fprintf ppf "w"
  | `i64 -> Format.fprintf ppf "l"

type imm = [
  | `i8
  | `i16
  | imm_base
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_imm : imm -> int = function
  | `i8 -> 8
  | `i16 -> 16
  | #imm_base as b -> sizeof_imm_base b

let pp_imm ppf : imm -> unit = function
  | `i8  -> Format.fprintf ppf "b"
  | `i16 -> Format.fprintf ppf "h"
  | #imm_base as i -> pp_imm_base ppf i

type fp = [
  | `f32
  | `f64
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_fp : fp -> int = function
  | `f32 -> 32
  | `f64 -> 32

let pp_fp ppf : fp -> unit = function
  | `f32 -> Format.fprintf ppf "s"
  | `f64 -> Format.fprintf ppf "d"

type basic = [
  | imm
  | fp
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_basic : basic -> int = function
  | #imm as i -> sizeof_imm i
  | #fp  as f -> sizeof_fp  f

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
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>%a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields

let pp_compound_decl ppf : compound -> unit = function
  | `compound (name, align, fields) ->
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Format.fprintf ppf "type :%s = " name;
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields

type special = [
  | `mem 
  | `flag
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_special ppf : special -> unit = function
  | `mem  -> Format.fprintf ppf "m"
  | `flag -> Format.fprintf ppf "f"

type arg = [
  | basic
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_arg ppf : arg -> unit = function
  | #basic as b -> Format.fprintf ppf "%a" pp_basic b
  | `name s -> Format.fprintf ppf ":%s" s

type proto = [
  | `proto of basic option * arg list * bool
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_proto ppf : proto -> unit = function
  | `proto (ret, args, variadic) ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    let pp_args = Format.pp_print_list ~pp_sep pp_arg in
    Option.iter ret ~f:(Format.fprintf ppf "%a " pp_basic);
    Format.fprintf ppf "(%a" pp_args args;
    match variadic, args with
    | false, _ -> Format.fprintf ppf ")"
    | true, [] -> Format.fprintf ppf "...)"
    | true, _  -> Format.fprintf ppf ", ...)"

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
