open Core
open Pseudo_common

type ('a, 'b) t = {
  name : string;
  blks : 'a Pseudo_blk.t ftree;
  rets : 'b ftree;
} [@@deriving bin_io, compare, equal, sexp]

let entry t = (Ftree.head_exn t.blks).label

let create_exn ~name ~blks ~rets = match blks with
  | [] ->
    invalid_argf
      "Cannot create function $%s with an empty list of blocks"
      name ()
  | blks -> {
      name;
      blks = Ftree.of_list blks;
      rets = Ftree.of_list rets;
    }

let create ~name ~blks ~rets =
  try Ok (create_exn ~name ~blks ~rets) with
  | Invalid_argument msg -> Or_error.error_string msg

let name t = t.name
let blks ?(rev = false) t = Ftree.enum ~rev t.blks
let rets ?(rev = false) t = Ftree.enum ~rev t.rets

let map_of_blks t =
  Ftree.fold t.blks ~init:Label.Tree.empty ~f:(fun acc b ->
      Label.Tree.set acc ~key:b.label ~data:b)

let update_blk fn b =
  let l = Pseudo_blk.label b in {
    fn with blks = Ftree.update_if fn.blks b ~f:(Fn.flip Pseudo_blk.has_label l);
  }

let update_blks' t blks =
  let blks = Ftree.map t.blks ~f:(fun b ->
      Label.Tree.find blks b.label |>
      Option.value ~default:b) in
  {t with blks}

let update_blks_exn t blks =
  List.fold blks ~init:Label.Tree.empty ~f:(fun acc b ->
      let key = Pseudo_blk.label b in
      match Label.Tree.add acc ~key ~data:b with
      | `Duplicate -> invalid_argf "Duplicate label %a" Label.pps key ()
      | `Ok m -> m) |> update_blks' t

let update_blks t blks =
  try Ok (update_blks_exn t blks) with
  | Invalid_argument msg -> Or_error.error_string msg

let pp ppa ppb ppf t =
  let sep_ret ppf = Format.fprintf ppf " " in
  let sep_blk ppf = Format.fprintf ppf "@;" in
  match Ftree.is_empty t.blks with
  | true ->
    Format.fprintf ppf "$%s:" t.name;
    if not @@ Ftree.is_empty t.rets then
      Format.fprintf ppf " ; returns: %a"
        (Ftree.pp ppb sep_ret) t.rets
  | false ->
    Format.fprintf ppf "$%s:" t.name;
    if not @@ Ftree.is_empty t.rets then
      Format.fprintf ppf " ; returns: %a"
        (Ftree.pp ppb sep_ret) t.rets;
    Format.fprintf ppf "@;@[<v 0>%a@]"
      (Ftree.pp (Pseudo_blk.pp ppa) sep_blk) t.blks
