open Core
open Pseudo_common

module Data = Virtual.Data
module Func = Pseudo_func

type ('a, 'b) t = {
  name : string;
  data : Data.t ftree;
  funs : ('a, 'b) Func.t ftree;
  dict : Dict.t;
} [@@deriving bin_io, compare, equal, sexp]

let create
    ?(dict = Dict.empty)
    ?(data = [])
    ?(funs = [])
    ~name
    () = {
  name;
  data = Ftree.of_list data;
  funs = Ftree.of_list funs;
  dict;
}

let name m = m.name
let data ?(rev = false) m = Ftree.enum m.data ~rev
let funs ?(rev = false) m = Ftree.enum m.funs ~rev
let has_name m name = String.(name = m.name)
let hash m = String.hash m.name
let dict fn = fn.dict
let with_dict fn dict = {fn with dict}
let with_tag fn tag x = {fn with dict = Dict.set fn.dict tag x}

exception Failed of Error.t

let insert_data m d = {
  m with data = Ftree.snoc m.data d;
}

let insert_fn m fn = {
  m with funs = Ftree.snoc m.funs fn;
}

let remove_data m name = {
  m with data = Ftree.remove_if m.data ~f:(Fn.flip Data.has_name name);
}

let remove_fn m name = {
  m with funs = Ftree.remove_if m.funs ~f:(Fn.flip Func.has_name name);
}

let map_data m ~f = {
  m with data = Ftree.map m.data ~f;
}

let map_funs m ~f = {
  m with funs = Ftree.map m.funs ~f;
}

let map_err_aux t ~f = Ftree.map t ~f:(fun x -> match f x with
    | Error e -> raise_notrace @@ Failed e
    | Ok x -> x)

let map_data_err m ~f =
  try  Ok {m with data = map_err_aux m.data ~f}
  with Failed err -> Error err

let map_funs_err m ~f =
  try  Ok {m with funs = map_err_aux m.funs ~f}
  with Failed err -> Error err

let with_funs m funs = {m with funs = Ftree.of_list funs}

let pp ppa ppb ppf m =
  let sep ppf = Format.fprintf ppf "@;@;" in
  let em = Ftree.is_empty in
  match em m.data, em m.funs with
  | true, true ->
    Format.fprintf ppf "@[<v 0>module %s@]" m.name
  | true, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp (Func.pp ppa ppb) sep) m.funs
  | false, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Data.pp sep) m.data
  | false, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Data.pp sep) m.data
      (Ftree.pp (Func.pp ppa ppb) sep) m.funs
