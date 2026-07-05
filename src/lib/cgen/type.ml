open Core

module Regular = Cgen_utils.Regular
module E = Cgen_utils.Monads.Error
module L = Layout

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
  | `f64 -> 64

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
  | `elt  of basic  * int
  | `name of string * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_field ppf : field -> unit = function
  | `elt  (t, 1) -> Format.fprintf ppf "%a" pp_basic t
  | `elt  (t, n) -> Format.fprintf ppf "%a %d" pp_basic t n
  | `name (s, 1) -> Format.fprintf ppf ":%s" s
  | `name (s, n) -> Format.fprintf ppf ":%s %d" s n

type compound = [
  | `struct_ of string * int option * field list
  | `union   of string * int option * field list
] [@@deriving bin_io, compare, equal, hash, sexp]

type named = [
  | compound
  | `opaque of string * int * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let named_name : named -> string = function
  | `struct_ (s, _, _)
  | `union (s, _, _)
  | `opaque (s, _, _) -> s

let named_align : named -> int option = function
  | `struct_ (_, a, _)
  | `union (_, a, _) -> a
  | `opaque (_, a, _) -> Some a

let pp_fields ppf align fields =
  let pp_sep ppf () = Format.fprintf ppf ",@;" in
  Option.iter align ~f:(Format.fprintf ppf "align %d ");
  if List.is_empty fields then
    Format.fprintf ppf "{}"
  else
    Format.fprintf ppf "{@;@[<v 2>%a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields

let pp_named ppf : named -> unit = function
  | `struct_ (_, align, fields) -> pp_fields ppf align fields
  | `union (_, align, fields) ->
    Format.fprintf ppf "union ";
    pp_fields ppf align fields
  | `opaque (_, align, n) ->
    Format.fprintf ppf "align %d {%d}" align n

let pp_fields_decl ppf align fields =
  let pp_sep ppf () = Format.fprintf ppf ",@;" in
  Option.iter align ~f:(Format.fprintf ppf "align %d ");
  if List.is_empty fields then
    Format.fprintf ppf "{}"
  else
    Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields

let pp_named_decl ppf : named -> unit = function
  | `struct_ (name, align, fields) ->
    Format.fprintf ppf "type :%s = " name;
    pp_fields_decl ppf align fields
  | `union (name, align, fields) ->
    Format.fprintf ppf "type :%s = union " name;
    pp_fields_decl ppf align fields
  | `opaque (name, align, n) ->
    Format.fprintf ppf "type :%s = align %d {%d}" name align n

type datum = [
  | basic
  | `pad    of int
  | `opaque of int
  | `union  of string * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_datum ppf : datum -> unit = function
  | #basic as b   -> Format.fprintf ppf "%a"  pp_basic b
  | `pad n        -> Format.fprintf ppf "%d"  n
  | `opaque n     -> Format.fprintf ppf "?%d" n
  | `union (u, _) -> Format.fprintf ppf ":%s" u

module Field = struct
  type t = field [@@deriving bin_io, compare, equal, hash, sexp]
  type nonrec datum = datum [@@deriving bin_io, compare, equal, hash, sexp]

  let pad n = `pad n
  let opaque n = `opaque n

  let datum_bytes : datum -> int = function
    | #basic as b -> sizeof_basic b / 8
    | `pad n | `opaque n | `union (_, n) -> n

  let try_merge a b = match a, b with
    | `pad a, `pad b -> Some (`pad (a + b))
    | `opaque a, `opaque b -> Some (`opaque (a + b))
    | _ -> None

  let refs : t -> string list = function
    | `elt _ -> []
    | `name (n, _) -> [n]

  let field_data ~gamma ~enclosing (f : t) =
    match f with
    | `elt (_, c) | `name (_, c) when c <= 0 ->
      invalid_argf "Invalid field %s for type :%s"
        (Format.asprintf "%a" pp_field f) enclosing ()
    | `elt (t, c) ->
      let s = sizeof_basic t / 8 in
      let d = List.init c ~f:(fun _ -> (t :> datum)) in
      d, s, s * c
    | `name (s, _) when String.(s = enclosing) ->
      invalid_argf "Type :%s is incomplete, it cannot \
                    contain itself as a field" enclosing ()
    | `name (s, c) -> match gamma s with
      | exception exn ->
        invalid_argf "Invalid argument :%s for gamma: %s"
          s (Exn.to_string exn) ()
      | l when L.align l <= 0 ->
        invalid_argf "Invalid alignment %d for type :%s" (L.align l) s ()
      | l when L.sizeof l = 0 ->
        (* Empty: preserve alignment. *)
        [], L.align l, 0
      | l ->
        let sz = L.sizeof l in
        let d = match L.members l with
          | First m ->
            List.init c ~f:(fun _ -> m) |> List.concat
          | Second _ ->
            List.init c ~f:(fun _ -> (`union (s, sz) : datum)) in
        d, L.align l, sz * c
end

let pp_data ppf ds =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  Format.pp_print_list ~pp_sep pp_datum ppf ds

let pp_layout ppf l = match L.members l with
  | First d ->
    Format.fprintf ppf "%d/%d(%a)" (L.align l) (L.sizeof l) pp_data d
  | Second ds ->
    let pp_sep ppf () = Format.fprintf ppf "; " in
    Format.fprintf ppf "%d/%d(%a)" (L.align l) (L.sizeof l)
      (Format.pp_print_list ~pp_sep pp_data) ds

let sizeof_layout = L.sizeof

module Layout = struct
  include L.Make(Field)

  let sizeof = L.sizeof
  let align = L.align
  let is_empty = L.is_empty
  let members = L.members

  include Regular.Make(struct
      type nonrec t = t [@@deriving bin_io, compare, equal, hash, sexp]
      let pp = pp_layout
    end)
end

type layout = Layout.t [@@deriving bin_io, compare, equal, hash, sexp]

let layout_exn = Layout.create

let layout g c = try Ok (layout_exn g c) with
  | Invalid_argument msg -> Or_error.error_string msg

let layouts_of_types_exn = Layout.of_types

let layouts_of_types ts = try Ok (layouts_of_types_exn ts) with
  | Invalid_argument msg -> Or_error.error_string msg

type arg = [
  | basic
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_arg ppf : arg -> unit = function
  | #basic as b -> Format.fprintf ppf "%a" pp_basic b
  | `name s -> Format.fprintf ppf ":%s" s

type ret = [
  | arg
  | `si8
  | `si16
  | `si32
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_ret ppf = function
  | #arg as a -> Format.fprintf ppf "%a" pp_arg a
  | `si8 -> Format.fprintf ppf "sb"
  | `si16 -> Format.fprintf ppf "sh"
  | `si32 -> Format.fprintf ppf "sw"

let same_ret (a : ret) (b : ret) = match a, b with
  | `i8, `si8 | `si8, `i8 -> true
  | `i16, `si16 | `si16, `i16 -> true
  | `i32, `si32 | `si32, `i32 -> true
  | _ -> equal_ret a b

let is_ret_signed : ret -> bool = function
  | `si8 | `si16 | `si32 -> true
  | _ -> false

type proto = [
  | `proto of ret option * arg list * bool
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_proto ppf : proto -> unit = function
  | `proto (ret, args, variadic) ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    let pp_args = Format.pp_print_list ~pp_sep pp_arg in
    Option.iter ret ~f:(Format.fprintf ppf "%a " pp_ret);
    Format.fprintf ppf "(%a" pp_args args;
    match variadic, args with
    | false, _ -> Format.fprintf ppf ")"
    | true, [] -> Format.fprintf ppf "...)"
    | true, _  -> Format.fprintf ppf ", ...)"

module T = struct
  type t = [
    | basic
    | named
    | `flag
  ] [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pp ppf : t -> unit = function
  | #basic as b -> Format.fprintf ppf "%a" pp_basic b
  | #named as c -> Format.fprintf ppf "%a" pp_named c
  | `flag       -> Format.fprintf ppf "flag"

include Regular.Make(struct
    include T
    let pp = pp
  end)
