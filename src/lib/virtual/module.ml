module Data_ = Data

open Core
open Regular.Std
open Common

module T = struct
  type t = {
    name : string;
    typs : Type.compound array;
    data : Data_.t array;
    funs : Func.t array;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create ?(typs = []) ?(data = []) ?(funs = []) ~name () = {
  name;
  typs = Array.of_list typs;
  data = Array.of_list data;
  funs = Array.of_list funs;
}

let name m = m.name
let typs ?(rev = false) m = Array.enum m.typs ~rev
let data ?(rev = false) m = Array.enum m.data ~rev
let funs ?(rev = false) m = Array.enum m.funs ~rev
let has_name m name = String.(name = m.name)
let hash m = String.hash m.name

exception Failed of Error.t

let insert_type m t = {
  m with typs = Array.push_back m.typs t;
}

let insert_data m d = {
  m with data = Array.push_back m.data d;
}

let insert_fn m fn = {
  m with funs = Array.push_back m.funs fn;
}

let remove_type m name = {
  m with typs = Array.remove_if m.typs ~f:(fun c ->
    String.equal name @@ Type.compound_name c);
}

let remove_data m name = {
  m with data = Array.remove_if m.data ~f:(Fn.flip Data_.has_name name);
}

let remove_fn m name = {
  m with funs = Array.remove_if m.funs ~f:(Fn.flip Func.has_name name);
}

let map_typs m ~f = {
  m with typs = Array.map m.typs ~f;
}

let map_data m ~f = {
  m with data = Array.map m.data ~f;
}

let map_funs m ~f = {
  m with funs = Array.map m.funs ~f;
}

let map_typs_err m ~f = try
    let typs = Array.map m.typs ~f:(fun t -> match f t with
        | Error e -> raise @@ Failed e
        | Ok t -> t) in
    Ok {m with typs}
  with Failed err -> Error err

let map_data_err m ~f = try
    let data = Array.map m.data ~f:(fun d -> match f d with
        | Error e -> raise @@ Failed e
        | Ok d -> d) in
    Ok {m with data}
  with Failed err -> Error err

let map_funs_err m ~f = try
    let funs = Array.map m.funs ~f:(fun fn -> match f fn with
        | Error e -> raise @@ Failed e
        | Ok fn -> fn) in
    Ok {m with funs}
  with Failed err -> Error err

let pp ppf m =
  let sep ppf = Format.fprintf ppf "@;@;" in
  match m.typs, m.data, m.funs with
  | [||], [||], [||] ->
    Format.fprintf ppf "@[<v 0>module %s@]" m.name
  | [||], [||], funs ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Array.pp Func.pp sep) funs
  | [||], data, [||] ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Array.pp Data_.pp sep) data
  | typs, [||], [||] ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (Array.pp Type.pp_compound_decl sep) typs
  | [||], data, funs ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Array.pp Data_.pp sep) data
      (Array.pp Func.pp sep) funs
  | typs, [||], funs ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Array.pp Type.pp_compound_decl sep) typs
      (Array.pp Func.pp sep) funs
  | typs, data, [||] ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Array.pp Type.pp_compound_decl sep) typs
      (Array.pp Data_.pp sep) data
  | typs, data, funs ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (Array.pp Type.pp_compound_decl sep) typs
      (Array.pp Data_.pp sep) data
      (Array.pp Func.pp sep) funs

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Module"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
