open Core
open Virtual_common
open Cgen_containers

module Regular = Cgen_utils.Regular

type elt = [
  | const
  | `string of string
  | `zero   of int
] [@@deriving bin_io, compare, equal, sexp]

let pp_elt ppf : elt -> unit = function
  | #const as c -> Format.fprintf ppf "%a" pp_const c
  | `string s -> Format.fprintf ppf "%S" s
  | `zero n -> Format.fprintf ppf "z %d" n

module T = struct
  type t = {
    name : string;
    elts : elt Rrb.t;
    dict : Dict.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

module Tag = struct
  let align = Dict.register "data-align" (module Int)

  let linkage = Dict.register "data-linkage" (module Linkage)

  let const = Dict.register "data-const" (module Unit)

  (* The symbol this one aliases (`__attribute__((alias(...)))`). An alias
     carries no elements; it is emitted as a symbol assignment. *)
  let alias = Dict.register "data-alias" (module String)
end

let create_exn
    ?(dict = Dict.empty)
    ~name
    ~elts
    () =
  match elts with
  | [] -> invalid_argf "Cannot create empty data %s" name ()
  | _ -> {name; elts = Rrb.of_list elts; dict}

let create
    ?(dict = Dict.empty)
    ~name
    ~elts
    () =
  try Ok (create_exn () ~name ~elts ~dict) with
  | Invalid_argument msg -> Or_error.error_string msg

(* An alias [name = target]: a symbol assignment with no storage, hence no
   elements. *)
let create_alias ?(dict = Dict.empty) ~name ~target () =
  {name; elts = Rrb.empty; dict = Dict.set dict Tag.alias target}

let name d = d.name

let elts ?(rev = false) d =
  if rev then Rrb.to_sequence_rev d.elts else Rrb.to_sequence d.elts

let linkage d = match Dict.find d.dict Tag.linkage with
  | None -> Linkage.default_static
  | Some l -> l

let align d = Dict.find d.dict Tag.align
let const d = Dict.mem d.dict Tag.const
let alias d = Dict.find d.dict Tag.alias
let dict d = d.dict
let with_dict d dict = {d with dict}
let with_tag d tag x = {d with dict = Dict.set d.dict tag x}
let has_name d name = String.(name = d.name)
let hash d = String.hash d.name

let typeof d ~(word : Type.imm_base) =
  let name = Format.sprintf "%s_t" d.name in
  let fields = Rrb.fold_right d.elts ~init:[] ~f:(fun elt fields ->
      Fn.flip List.cons fields @@ match elt with
      | `bool _     -> `elt (`i8, 1)
      | `int (_, t) -> `elt ((t :> Type.basic), 1)
      | `float _    -> `elt (`f32, 1)
      | `double _   -> `elt (`f64, 1)
      | `string s   -> `elt (`i8, String.length s)
      | `zero n     -> `elt (`i8, n)
      | `sym _      -> `elt ((word :> Type.basic), 1)) in
  `struct_ (name, align d, fields)

let prepend_elt d e = {
  d with elts = Rrb.cons e d.elts;
}

let append_elt d e = {
  d with elts = Rrb.snoc d.elts e;
}

let map_elts d ~f = {
  d with elts = Rrb.map d.elts ~f;
}

let pp_rrb pp_elt sep ppf t =
  let first = ref true in
  Rrb.iter t ~f:(fun x ->
      if !first then first := false else sep ppf;
      pp_elt ppf x)

let pp ppf d =
  let sep ppf = Format.fprintf ppf ",@;" in
  let lnk = linkage d in
  if Linkage.export lnk
  || Linkage.section lnk |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp lnk;
  if const d then Format.fprintf ppf "const ";
  Format.fprintf ppf "data $%s = " d.name;
  Option.iter (align d) ~f:(Format.fprintf ppf "align %d ");
  Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
    (pp_rrb pp_elt sep) d.elts

include Regular.Make(struct
    include T
    let pp = pp
    let hash = hash
  end)
