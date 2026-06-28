open Core
open Cgen_containers

module Data = Virtual.Data
module Func = Pseudo_func

type ('a, 'b) t = {
  name : string;
  data : Data.t Rrb.t;
  funs : ('a, 'b) Func.t Rrb.t;
  dict : Dict.t;
} [@@deriving bin_io, compare, equal, sexp]

let create
    ?(dict = Dict.empty)
    ?(data = [])
    ?(funs = [])
    ~name
    () = {
  name;
  data = Rrb.of_list data;
  funs = Rrb.of_list funs;
  dict;
}

let name m = m.name

let data ?(rev = false) m =
  if rev then Rrb.to_sequence_rev m.data else Rrb.to_sequence m.data

let funs ?(rev = false) m =
  if rev then Rrb.to_sequence_rev m.funs else Rrb.to_sequence m.funs

let has_name m name = String.(name = m.name)
let hash m = String.hash m.name
let dict fn = fn.dict
let with_dict fn dict = {fn with dict}
let with_tag fn tag x = {fn with dict = Dict.set fn.dict tag x}

exception Failed of Error.t

let insert_data m d = {
  m with data = Rrb.snoc m.data d;
}

let insert_fn m fn = {
  m with funs = Rrb.snoc m.funs fn;
}

let remove_data m name = {
  m with data = Rrb.filter m.data ~f:(fun d -> not @@ Data.has_name d name);
}

let remove_fn m name = {
  m with funs = Rrb.filter m.funs ~f:(fun fn -> not @@ Func.has_name fn name);
}

let map_data m ~f = {
  m with data = Rrb.map m.data ~f;
}

let map_funs m ~f = {
  m with funs = Rrb.map m.funs ~f;
}

let map_err_aux t ~f = Rrb.map t ~f:(fun x -> match f x with
    | Error e -> raise_notrace @@ Failed e
    | Ok x -> x)

let map_data_err m ~f =
  try  Ok {m with data = map_err_aux m.data ~f}
  with Failed err -> Error err

let map_funs_err m ~f =
  try  Ok {m with funs = map_err_aux m.funs ~f}
  with Failed err -> Error err

let with_funs m funs = {m with funs = Rrb.of_list funs}

let pp_rrb = Func.pp_rrb

let pp ppa ppb ppf m =
  let sep ppf = Format.fprintf ppf "@;@;" in
  let em = Rrb.is_empty in
  match em m.data, em m.funs with
  | true, true ->
    Format.fprintf ppf "@[<v 0>module %s@]" m.name
  | true, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb (Func.pp ppa ppb) sep) m.funs
  | false, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Data.pp sep) m.data
  | false, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Data.pp sep) m.data
      (pp_rrb (Func.pp ppa ppb) sep) m.funs
