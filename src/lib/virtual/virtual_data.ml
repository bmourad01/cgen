open Core
open Regular.Std
open Virtual_common

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
    elts : elt ftree;
    dict : Dict.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

module Tag = struct
  let align = Dict.register
      ~uuid:"e1099f19-c478-4e89-a462-15af393068ad"
      "data-align" (module Int)

  let linkage = Dict.register
      ~uuid:"c3c1ad03-b3d7-42b5-8529-b21b7d04173b"
      "data-linkage" (module Linkage)

  let const = Dict.register
      ~uuid:"41f13eba-baa9-44c4-96cc-4729aaf1eb55"
      "data-const" (module Unit)
end

let create_exn
    ?(dict = Dict.empty)
    ~name
    ~elts
    () =
  match elts with
  | [] -> invalid_argf "Cannot create empty data %s" name ()
  | _ -> {name; elts = Ftree.of_list elts; dict}

let create
    ?(dict = Dict.empty)
    ~name
    ~elts
    () =
  try Ok (create_exn () ~name ~elts ~dict) with
  | Invalid_argument msg -> Or_error.error_string msg

let name d = d.name
let elts ?(rev = false) d = Ftree.enum d.elts ~rev

let linkage d = match Dict.find d.dict Tag.linkage with
  | None -> Linkage.default_export
  | Some l -> l

let align d = Dict.find d.dict Tag.align
let const d = Dict.mem d.dict Tag.const
let dict d = d.dict
let with_dict d dict = {d with dict}
let with_tag d tag x = {d with dict = Dict.set d.dict tag x}
let has_name d name = String.(name = d.name)
let hash d = String.hash d.name

let typeof d ~(word : Type.imm_base) =
  let name = Format.sprintf "%s_t" d.name in
  let fields = Ftree.fold_right d.elts ~init:[] ~f:(fun elt fields ->
      Fn.flip List.cons fields @@ match elt with
      | `bool _     -> `elt (`i8, 1)
      | `int (_, t) -> `elt ((t :> Type.basic), 1)
      | `float _    -> `elt (`f32, 1)
      | `double _   -> `elt (`f64, 1)
      | `string s   -> `elt (`i8, String.length s)
      | `zero n     -> `elt (`i8, n)
      | `sym _      -> `elt ((word :> Type.basic), 1)) in
  `compound (name, align d, fields)

let prepend_elt d e = {
  d with elts = Ftree.cons d.elts e;
}

let append_elt d e = {
  d with elts = Ftree.snoc d.elts e;
}

let map_elts d ~f = {
  d with elts = Ftree.map d.elts ~f;
}

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
    (Ftree.pp pp_elt sep) d.elts

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Data"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
