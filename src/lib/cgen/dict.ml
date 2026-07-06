open Core

module type S = sig
  type t [@@deriving bin_io, compare, sexp]
  val pp : Format.formatter -> t -> unit
end

module H = Cgen_containers.Hdict.Make(struct
    type t = string
    let to_string = Fn.id
  end)

type 'a tag = 'a H.Key.t

let pp_tag ppf k = H.pp_key ppf k

type t = H.t

let empty = H.empty
let set d k v = H.set k v d
let singleton k v = H.singleton k v
let remove d k = H.remove k d
let mem d k = H.mem k d
let find d k = H.find k d

type slot_io = {
  reader  : string -> t -> t;
  writer  : t -> string option;
  of_sexp : Sexp.t -> t -> t;
}

let io : slot_io String.Table.t = String.Table.create ()

let register (type a) ~uuid name (module S : S with type t = a) : a tag =
  let typeid = sprintf "%s:%s" uuid name in
  let key = H.Key.create ~name:typeid S.sexp_of_t in
  Hashtbl.set io ~key:typeid ~data:{
    reader = (fun s d -> H.set key (Binable.of_string (module S) s) d);
    writer = (fun d -> Option.map (H.find key d) ~f:(Binable.to_string (module S)));
    of_sexp = (fun s d -> H.set key (S.t_of_sexp s) d);
  };
  key

let sexp_of_t = H.sexp_of_t

let t_of_sexp = function
  | Sexp.List entries ->
    List.fold entries ~init:empty ~f:(fun d -> function
        | Sexp.List [Sexp.Atom typeid; vs] ->
          Hashtbl.find io typeid |> Option.value_map
            ~default:d ~f:(fun io -> io.of_sexp vs d)
        | other ->
          Sexplib0.Sexp_conv.of_sexp_error "Dict.t_of_sexp: bad entry" other)
  | other -> Sexplib0.Sexp_conv.of_sexp_error "Dict.t_of_sexp: expected a list" other

let compare x y = Sexp.compare (sexp_of_t x) (sexp_of_t y)
let equal x y = compare x y = 0

module Repr = struct
  type entry = {
    typeid : string;
    data   : string;
  } [@@deriving bin_io]

  type t = entry list [@@deriving bin_io]
end

include Binable.Of_binable_with_uuid(Repr)(struct
    type nonrec t = t

    let caller_identity = Bin_prot.Shape.Uuid.of_string
        "8f2e4c1a-6b3d-4e7f-9a0c-1d2e3f4a5b6c"

    let to_binable d =
      H.foreach d ~init:[] {
        visit = fun k _ acc ->
          let typeid = H.Key.name k in
          match Hashtbl.find io typeid with
          | None -> acc
          | Some io -> match io.writer d with
            | Some data -> Repr.{typeid; data} :: acc
            | None -> acc
      }

    let of_binable entries =
      List.fold entries ~init:empty ~f:(fun d {Repr.typeid; data} ->
          match Hashtbl.find io typeid with
          | Some io -> io.reader data d
          | None -> d)
  end)
