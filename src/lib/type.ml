open Core
open Monads.Std
open Regular.Std
open Graphlib.Std

module E = Monad.Result.Error

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
  | `elt  of basic  * int
  | `name of string * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_field ppf : field -> unit = function
  | `elt  (t, 1) -> Format.fprintf ppf "%a" pp_basic t
  | `elt  (t, n) -> Format.fprintf ppf "%a %d" pp_basic t n
  | `name (s, 1) -> Format.fprintf ppf ":%s" s
  | `name (s, n) -> Format.fprintf ppf ":%s %d" s n

type compound = [
  | `compound of string * int option * field list
  | `opaque   of string * int * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let compound_name : compound -> string = function
  | `compound (s, _, _)
  | `opaque (s, _, _) -> s

let compound_align : compound -> int option = function
  | `compound (_, a, _) -> a
  | `opaque (_, a, _) -> Some a

let pp_compound ppf : compound -> unit = function
  | `compound (_, align, fields) ->
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    if List.is_empty fields then
      Format.fprintf ppf "{}"
    else
      Format.fprintf ppf "{@;@[<v 2>%a@]@;}"
        (Format.pp_print_list ~pp_sep pp_field) fields
  | `opaque (_, align, n) ->
    Format.fprintf ppf "align %d {%d}" align n

let pp_compound_decl ppf : compound -> unit = function
  | `compound (name, align, fields) ->
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Format.fprintf ppf "type :%s = " name;
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    if List.is_empty fields then
      Format.fprintf ppf "{}"
    else
      Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
        (Format.pp_print_list ~pp_sep pp_field) fields
  | `opaque (name, align, n) ->
    Format.fprintf ppf "type :%s = align %d {%d}" name align n

type datum = [
  | basic
  | `pad    of int
  | `opaque of int
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_datum ppf : datum -> unit = function
  | #basic as b -> Format.fprintf ppf "%a"  pp_basic b
  | `pad n      -> Format.fprintf ppf "%d"  n
  | `opaque n   -> Format.fprintf ppf "?%d" n

type data = datum array [@@deriving bin_io, compare, equal, sexp]

module Data = Regular.Make(struct
    type t = data [@@deriving bin_io, compare, equal, sexp]

    let pp ppf ds =
      let last = Array.length ds - 1 in
      Array.iteri ds ~f:(fun i d ->
          Format.fprintf ppf "%a" pp_datum d;
          if i < last then Format.fprintf ppf ", ")

    let module_name = Some "Cgen.Type.Data"
    let version = "0.1"
    let hash x = String.hash @@ Format.asprintf "%a" pp x
  end)

let hash_fold_data = Data.hash_fold_t

type layout = {
  align : int;
  data  : data;
} [@@deriving bin_io, compare, equal, hash, sexp]

let pp_layout ppf l =
  Format.fprintf ppf "%d(%a)" l.align Data.pp l.data

let sizeof_layout l = Array.fold l.data ~init:0 ~f:(fun sz -> function
    | #basic as b -> sz + (sizeof_basic b / 8)
    | `pad n | `opaque n -> sz + n)

module Layout = struct
  type t = layout

  let sizeof = sizeof_layout
  let align l = l.align
  let data l = Array.to_sequence l.data
  let is_empty l = Array.is_empty l.data

  (* pre: `align` is a positive power of 2 *)
  let padding size align =
    let a = align - 1 in
    ((size + a) land lnot a) - size

  (* pre: the list is accumulated in reverse *)
  let padded data = function
    | 0 -> data | p -> `pad p :: data

  (* pre: the list is accumulated in reverse *)
  let coalesce =
    let rec aux acc = function
      | [] -> acc
      | `pad a :: `pad b :: ds ->
        aux acc @@ `pad (a + b) :: ds
      | `opaque a :: `opaque b :: ds ->
        aux acc @@ `opaque (a + b) :: ds
      | d :: ds -> aux (d :: acc) ds in
    aux []

  let finalize data align size =
    padding size align |> padded data |> coalesce |> Array.of_list

  let create gamma : compound -> layout = function
    | `opaque (s, n, _) | `compound (s, Some n, _)
      when n < 1 || (n land (n - 1)) <> 0 ->
      invalid_argf "Invalid alignment %d for type :%s, \
                    must be positive power of 2" n s ()
    | `opaque (s, _, n) when n < 0 ->
      invalid_argf "Invalid number of bytes %d for opaque type :%s" n s ()
    | `opaque (_, align, 0) -> {align; data = [|`pad align|]}
    | `opaque (_, align, n) ->
      {align; data = Array.of_list @@ padded [`opaque n] @@ padding n align}
    | `compound (_, Some n, []) -> {align = n; data = [|`pad n|]}
    | `compound (_, None, []) -> {align = 0; data = [||]}
    | `compound (name, align, fields) ->
      let data, align, size =
        let init = [], Option.value align ~default:1, 0 in
        List.fold fields ~init ~f:(fun (data, align, size) f ->
            let fdata, falign, fsize = match f with
              | `elt (_, c) | `name (_, c) when c <= 0 ->
                invalid_argf "Invalid field %s for type :%s"
                  (Format.asprintf "%a" pp_field f) name ()
              | `elt (t, c) ->
                let s = sizeof_basic t / 8 in
                let d = List.init c ~f:(fun _ -> (t :> datum)) in
                d, s, s * c
              | `name (s, c) -> match gamma s with
                | exception exn ->
                  invalid_argf "Invalid argument :%s for gamma: %s"
                    s (Exn.to_string exn) ()
                | {align = a; _} when a <= 0 ->
                  invalid_argf "Invalid alignment %d for type :%s" a s ()
                | {align; data} as l ->
                  let data = Array.to_list data in
                  let data = List.init c ~f:(fun _ -> data) |> List.concat in
                  data, align, sizeof l * c in
            let align = max align falign in
            let pad = padding size align in
            let data = List.rev_append fdata @@ padded data pad in
            data, align, size + pad + fsize) in
      {align; data = finalize data align size}

  module Typegraph = Graphlib.Make(String)(Unit)

  let build_tenv (ts : compound list) =
    List.fold ts ~init:String.Map.empty ~f:(fun tenv t ->
        let name = match t with
          | `opaque (name, _, _) -> name
          | `compound (name, _, _) -> name in
        match Map.add tenv ~key:name ~data:t with
        | `Duplicate -> invalid_argf "Duplicate type :%s" name ()
        | `Ok tenv -> tenv)

  let build_typ_graph tenv ts =
    List.fold ts ~init:Typegraph.empty ~f:(fun g -> function
        | `opaque (name, _, _) -> Typegraph.Node.insert name g
        | `compound (name, _, fields) ->
          let init = Typegraph.Node.insert name g in
          List.fold fields ~init ~f:(fun g -> function
              | `elt _ -> g
              | `name (n, _) when Map.mem tenv n ->
                Typegraph.Edge.(insert (create n name ()) g)
              | `name (n, _) ->
                invalid_argf "Undeclared type field :%s in type :%s"
                  n name ()))

  let check_typ_cycles g =
    Graphlib.strong_components (module Typegraph) g |>
    Partition.groups |> Seq.iter ~f:(fun grp ->
        match Seq.to_list @@ Group.enum grp with
        | [] -> ()
        | [name] ->
          let succs = Typegraph.Node.succs name g in
          if Seq.mem succs name ~equal:String.equal
          then invalid_argf "Cycle detected in type :%s" name ()
        | xs ->
          invalid_argf "Cycle detected in types %s"
            (List.to_string ~f:(fun s -> ":" ^ s) xs)
            ())

  let layouts tenv g =
    let genv = String.Table.create () in
    Graphlib.reverse_postorder_traverse (module Typegraph) g |>
    Seq.map ~f:(fun name ->
        let t = Map.find_exn tenv name in
        let gamma name = match Hashtbl.find genv name with
          | None -> invalid_argf "Type :%s not found in gamma" name ()
          | Some l -> l in
        let l = create gamma t in
        Hashtbl.set genv ~key:name ~data:l;
        name, l) |> Seq.to_list

  let of_types ts =
    let tenv = build_tenv ts in
    let g = build_typ_graph tenv ts in
    check_typ_cycles g;
    layouts tenv g

  include Regular.Make(struct
      type t = layout [@@deriving bin_io, compare, equal, hash, sexp]
      let pp = pp_layout
      let version = "0.1"
      let module_name = Some "Cgen.Type.Layout"
    end)
end

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

type proto = [
  | `proto of arg option * arg list * bool
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_proto ppf : proto -> unit = function
  | `proto (ret, args, variadic) ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    let pp_args = Format.pp_print_list ~pp_sep pp_arg in
    Option.iter ret ~f:(Format.fprintf ppf "%a " pp_arg);
    Format.fprintf ppf "(%a" pp_args args;
    match variadic, args with
    | false, _ -> Format.fprintf ppf ")"
    | true, [] -> Format.fprintf ppf "...)"
    | true, _  -> Format.fprintf ppf ", ...)"

module T = struct
  type t = [
    | basic
    | compound
    | `flag
  ] [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pp ppf : t -> unit = function
  | #basic    as b -> Format.fprintf ppf "%a" pp_basic b
  | #compound as c -> Format.fprintf ppf "%a" pp_compound c
  | `flag          -> Format.fprintf ppf "flag"

include Regular.Make(struct
    include T

    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Type"
  end)
