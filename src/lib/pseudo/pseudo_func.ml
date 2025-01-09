open Core
open Pseudo_common

type 'a t = {
  name : string;
  blks : 'a Pseudo_blk.t ftree;
} [@@deriving bin_io, compare, equal, sexp]

let create ~name ~blks = {
  name;
  blks = Ftree.of_list blks;
}

let name t = t.name
let blks ?(rev = false) t = Ftree.enum ~rev t.blks

let map_of_blks t =
  Ftree.fold t.blks ~init:Label.Tree.empty ~f:(fun acc b ->
      Label.Tree.set acc ~key:b.label ~data:b)

let pp ppa ppf t =
  let sep ppf = Format.fprintf ppf "@;" in
  match Ftree.is_empty t.blks with
  | true ->
    Format.fprintf ppf "$%s:" t.name
  | false ->
    Format.fprintf ppf "$%s:@;@[<v 0>%a@]"
      t.name (Ftree.pp (Pseudo_blk.pp ppa) sep) t.blks
