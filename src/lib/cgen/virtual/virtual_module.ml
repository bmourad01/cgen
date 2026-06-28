open Core
open Regular.Std
open Virtual_common
open Cgen_containers

module Func = Virtual_func
module Data = Virtual_data

module T = struct
  type t = {
    name : string;
    typs : Type.named Rrb.t;
    data : Data.t Rrb.t;
    funs : Func.t Rrb.t;
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
  typs = Rrb.of_list typs;
  data = Rrb.of_list data;
  funs = Rrb.of_list funs;
  dict;
}

let name m = m.name

let typs ?(rev = false) m =
  if rev then Rrb.to_sequence_rev m.typs else Rrb.to_sequence m.typs

let data ?(rev = false) m =
  if rev then Rrb.to_sequence_rev m.data else Rrb.to_sequence m.data

let funs ?(rev = false) m =
  if rev then Rrb.to_sequence_rev m.funs else Rrb.to_sequence m.funs

let fold_field t ?(rev = false) ~init ~f =
  if rev then Rrb.fold_right t ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold t ~init ~f

let iter_field t ?(rev = false) ~f () =
  if rev then Rrb.iter_rev t ~f else Rrb.iter t ~f

let fold_typs ?rev m ~init ~f = fold_field m.typs ?rev ~init ~f
let fold_data ?rev m ~init ~f = fold_field m.data ?rev ~init ~f
let fold_funs ?rev m ~init ~f = fold_field m.funs ?rev ~init ~f

let iter_typs ?rev m ~f = iter_field m.typs ?rev ~f ()
let iter_data ?rev m ~f = iter_field m.data ?rev ~f ()
let iter_funs ?rev m ~f = iter_field m.funs ?rev ~f ()

let has_name m name = String.(name = m.name)
let hash m = String.hash m.name
let dict fn = fn.dict
let with_dict fn dict = {fn with dict}
let with_tag fn tag x = {fn with dict = Dict.set fn.dict tag x}

exception Failed of Error.t

let insert_type m t = {
  m with typs = Rrb.snoc m.typs t;
}

let insert_data m d = {
  m with data = Rrb.snoc m.data d;
}

let insert_fn m fn = {
  m with funs = Rrb.snoc m.funs fn;
}

let remove_type m name = {
  m with typs = Rrb.filter m.typs ~f:(fun c ->
    not @@ String.equal name @@ Type.named_name c);
}

let remove_data m name = {
  m with data = Rrb.filter m.data ~f:(fun d ->
    not @@ Data.has_name d name);
}

let remove_fn m name = {
  m with funs = Rrb.filter m.funs ~f:(fun fn ->
    not @@ Func.has_name fn name);
}

let map_typs m ~f = {
  m with typs = Rrb.map m.typs ~f;
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

let map_typs_err m ~f =
  try  Ok {m with typs = map_err_aux m.typs ~f}
  with Failed err -> Error err

let map_data_err m ~f =
  try  Ok {m with data = map_err_aux m.data ~f}
  with Failed err -> Error err

let map_funs_err m ~f =
  try  Ok {m with funs = map_err_aux m.funs ~f}
  with Failed err -> Error err

let with_funs m funs = {m with funs = Rrb.of_list funs}

let pp_rrb = Data.pp_rrb

let pp ppf m =
  let sep ppf = Format.fprintf ppf "@;@;" in
  let em = Rrb.is_empty in
  match em m.typs, em m.data, em m.funs with
  | true, true, true ->
    Format.fprintf ppf "@[<v 0>module %s@]" m.name
  | true, true, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Func.pp sep) m.funs
  | true, false, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Data.pp sep) m.data
  | false, true, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Type.pp_named_decl sep) m.typs
  | true, false, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Data.pp sep) m.data
      (pp_rrb Func.pp sep) m.funs
  | false, true, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Type.pp_named_decl sep) m.typs
      (pp_rrb Func.pp sep) m.funs
  | false, false, true ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Type.pp_named_decl sep) m.typs
      (pp_rrb Data.pp sep) m.data
  | false, false, false ->
    Format.fprintf ppf "@[<v 0>module %s@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@;@;\
                        @[<v 0>%a@]@]" m.name
      (pp_rrb Type.pp_named_decl sep) m.typs
      (pp_rrb Data.pp sep) m.data
      (pp_rrb Func.pp sep) m.funs

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Module"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
