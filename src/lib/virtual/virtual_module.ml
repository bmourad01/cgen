open Core
open Regular.Std
open Virtual_common

module Func = Virtual_func
module Data = Virtual_data

module T = struct
  type t = {
    name : string;
    typs : Type.compound ftree;
    data : Data.t ftree;
    funs : Func.t ftree;
    dict : Dict.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create
    ?(dict = Dict.empty)
    ?(typs = [])
    ?(data = [])
    ?(funs = [])
    ~name
    () = {
  name;
  typs = Ftree.of_list typs;
  data = Ftree.of_list data;
  funs = Ftree.of_list funs;
  dict;
}

let name m = m.name
let typs ?(rev = false) m = Ftree.enum m.typs ~rev
let data ?(rev = false) m = Ftree.enum m.data ~rev
let funs ?(rev = false) m = Ftree.enum m.funs ~rev
let has_name m name = String.(name = m.name)
let hash m = String.hash m.name
let dict fn = fn.dict
let with_dict fn dict = {fn with dict}
let with_tag fn tag x = {fn with dict = Dict.set fn.dict tag x}

exception Failed of Error.t

let insert_type m t = {
  m with typs = Ftree.snoc m.typs t;
}

let insert_data m d = {
  m with data = Ftree.snoc m.data d;
}

let insert_fn m fn = {
  m with funs = Ftree.snoc m.funs fn;
}

let remove_type m name = {
  m with typs = Ftree.remove_if m.typs ~f:(fun c ->
    String.equal name @@ Type.compound_name c);
}

let remove_data m name = {
  m with data = Ftree.remove_if m.data ~f:(Fn.flip Data.has_name name);
}

let remove_fn m name = {
  m with funs = Ftree.remove_if m.funs ~f:(Fn.flip Func.has_name name);
}

let map_typs m ~f = {
  m with typs = Ftree.map m.typs ~f;
}

let map_data m ~f = {
  m with data = Ftree.map m.data ~f;
}

let map_funs m ~f = {
  m with funs = Ftree.map m.funs ~f;
}

let map_typs_err m ~f = try
    let typs = Ftree.map m.typs ~f:(fun t -> match f t with
        | Error e -> raise @@ Failed e
        | Ok t -> t) in
    Ok {m with typs}
  with Failed err -> Error err

let map_data_err m ~f = try
    let data = Ftree.map m.data ~f:(fun d -> match f d with
        | Error e -> raise @@ Failed e
        | Ok d -> d) in
    Ok {m with data}
  with Failed err -> Error err

let map_funs_err m ~f = try
    let funs = Ftree.map m.funs ~f:(fun fn -> match f fn with
        | Error e -> raise @@ Failed e
        | Ok fn -> fn) in
    Ok {m with funs}
  with Failed err -> Error err

let with_funs m funs = {m with funs = Ftree.of_list funs}

let pp ppf m =
  let sep ppf = Format.fprintf ppf "@;@;" in
  let em = Ftree.is_empty in
  match em m.typs, em m.data, em m.funs with
  | true, true, true ->
    Format.fprintf ppf "@[<v 0>module %s@]" m.name
  | true, true, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Func.pp sep) m.funs
  | true, false, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Data.pp sep) m.data
  | false, true, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Type.pp_compound_decl sep) m.typs
  | true, false, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Data.pp sep) m.data
      (Ftree.pp Func.pp sep) m.funs
  | false, true, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Type.pp_compound_decl sep) m.typs
      (Ftree.pp Func.pp sep) m.funs
  | false, false, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Type.pp_compound_decl sep) m.typs
      (Ftree.pp Data.pp sep) m.data
  | false, false, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Ftree.pp Type.pp_compound_decl sep) m.typs
      (Ftree.pp Data.pp sep) m.data
      (Ftree.pp Func.pp sep) m.funs

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Module"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
