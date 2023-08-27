(* Adapted from BAP. *)

open Core
open Regular.Std

module type S = sig
  type t [@@deriving bin_io, compare, sexp]
  val pp : Format.formatter -> t -> unit
end

module Uid = Type_equal.Id.Uid
module Typeid = String

type typeid = Typeid.t [@@deriving bin_io, compare, equal, sexp]

type 'a tag = {
  key : 'a Type_equal.Id.t;
} [@@unboxed]

type value = Univ_map.Packed.t = T : 'a Type_equal.Id.t * 'a -> value

module Equal = struct
  let proof = Type_equal.Id.same_witness_exn
  let try_prove = Type_equal.Id.same_witness
end

type type_info = {
  pp        : Format.formatter -> value -> unit;
  of_string : string -> value;
  to_string : value -> string;
  of_sexp   : Sexp.t -> value;
  to_sexp   : value -> Sexp.t;
  compare   : value -> value -> int;
}

let types : (typeid, type_info) Hashtbl.t =
  Hashtbl.create (module Typeid)

let uid = Type_equal.Id.uid

let register (type a) ~uuid name
    (module S : S with type t = a) : a tag =
  let name = Format.sprintf "%s:%s" uuid name in
  let key = Type_equal.Id.create ~name S.sexp_of_t in
  let pp ppf (T (k, x)) =
    let T = Equal.proof k key in
    S.pp ppf x in
  let of_string s = T (key, Binable.of_string (module S) s) in
  let to_string (T (k, x)) =
    let T = Equal.proof k key in
    Binable.to_string (module S) x in
  let of_sexp s = T (key, S.t_of_sexp s) in
  let to_sexp (T (k, x)) =
    let T = Equal.proof k key in
    S.sexp_of_t x in
  let compare (T (kx, x)) (T (ky, y)) =
    match Equal.try_prove kx ky with
    | None -> Uid.compare (uid kx) (uid ky)
    | Some T ->
      let T = Equal.proof kx key in
      S.compare x y in
  Hashtbl.add_exn types ~key:name ~data:{
    pp; of_string; to_string; of_sexp; to_sexp; compare;
  };
  {key}

let key_name k =
  let k = Type_equal.Id.name k in
  let i = Typeid.index_exn k ':' in
  String.subo ~pos:(i + 1) k

let key_typeid k = Type_equal.Id.name k
let tagname (T (k, _)) = key_name k
let typeid (T (k, _)) = key_typeid k

let info typeid =
  Hashtbl.find_and_call types typeid
    ~if_found:Fn.id
    ~if_not_found:(fun typeid ->
        invalid_argf "Can't deserialize type %s, \
                      as it is no longer known to the system"
          typeid ())

let ops x = info @@ typeid x
let compare_value x y = (ops x).compare x y
let equal_value x y = compare_value x y = 0

let sexp_of_value x = Sexp.List [
    Sexp.Atom (typeid x);
    (ops x).to_sexp x;
  ]

let value_of_sexp = function
  | Sexp.List [Atom typeid; repr] ->
    (info typeid).of_sexp repr
  | _ -> invalid_arg "value_of_sexp: broken representation"

let create {key} x = T (key, x)
let is {key} (T (k, _)) = Type_equal.Id.same key k

let get : type a. a tag -> value -> a option =
  fun {key} (T (k, x)) ->
  if Type_equal.Id.same key k then
    let T = Equal.proof key k in
    Some x
  else None

let get_exn : type a. a tag -> value -> a =
  fun {key} (T (k, x)) ->
  let T = Equal.proof key k in
  x

let pp_value ppf v = (ops v).pp ppf v

type t = Univ_map.t

let empty = Univ_map.empty
let is_empty = Univ_map.is_empty
let set d {key} x = Univ_map.set d ~key ~data:x
let remove d {key} = Univ_map.remove d key
let mem d {key} = Univ_map.mem d key
let find d {key} = Univ_map.find d key
let add d {key} x = Univ_map.add d ~key ~data:x
let change d {key} ~f = Univ_map.change d key ~f
let data d = Univ_map.to_alist d |> Seq.of_list
let to_sequence d = data d |> Seq.map ~f:(fun v -> typeid v, v)

let filter t ~f =
  data t |> Seq.fold ~init:empty ~f:(fun d (T (k, x) as v) ->
      if f v then Univ_map.set d ~key:k ~data:x else d)

let compare x y =
  compare_list compare_value
    (Univ_map.to_alist x)
    (Univ_map.to_alist y)

let equal x y = compare x y = 0

module Univ = struct
  type t = value
  let sexp_of_t = sexp_of_value
  let t_of_sexp = value_of_sexp

  module Repr = struct
    type t = {
      typeid : string;
      data : string;
    } [@@deriving bin_io]
  end

  include Binable.Of_binable(Repr)(struct
      type t = value
      let to_binable x = Repr.{
          typeid = typeid x;
          data = (ops x).to_string x;
        }
      let of_binable {Repr.typeid; data} =
        (info typeid).of_string data
    end) [@@warning "-D"]
end

module Data = struct
  type t = Univ.t list [@@deriving bin_io, sexp]
  let of_dict = Univ_map.to_alist
  let to_dict = List.fold ~init:empty ~f:(fun d (T (k,x)) ->
      Univ_map.set d ~key:k ~data:x)
end

include Binable.Of_binable(Data)(struct
    type t = Univ_map.t
    let to_binable = Data.of_dict
    let of_binable = Data.to_dict
  end) [@@warning "-D"]

include Sexpable.Of_sexpable(Data)(struct
    type t = Univ_map.t
    let to_sexpable = Data.of_dict
    let of_sexpable = Data.to_dict
  end)
