open Core
open Regular.Std
open Pseudo_common

module Slot = Virtual.Slot

module Tag = struct
  let needs_stack_frame = Dict.register
      ~uuid:"bd4f4a42-723a-4d31-b0ab-e63ba432a9e5"
      "pseudo-fn-needs-stack-frame" (module Unit)
end

type ('a, 'b) t = {
  name  : string;
  slots : Slot.t ftree;
  blks  : 'a Pseudo_blk.t ftree;
  rets  : 'b ftree;
  dict  : Dict.t;
} [@@deriving bin_io, compare, equal, sexp]

let entry t = (Ftree.head_exn t.blks).label

let create_exn
    ?(dict = Dict.empty)
    ?(slots = [])
    ~name
    ~blks
    ~rets
    () = match blks with
  | [] ->
    invalid_argf
      "Cannot create function $%s with an empty list of blocks"
      name ()
  | blks -> {
      name;
      slots = Ftree.of_list slots;
      blks = Ftree.of_list blks;
      rets = Ftree.of_list rets;
      dict;
    }

let create
    ?(dict = Dict.empty)
    ?(slots = [])
    ~name
    ~blks
    ~rets
    () =
  try Ok (create_exn ~dict ~slots ~name ~blks ~rets ()) with
  | Invalid_argument msg -> Or_error.error_string msg

let name t = t.name
let slots ?(rev = false) t = Ftree.enum ~rev t.slots
let blks ?(rev = false) t = Ftree.enum ~rev t.blks
let rets ?(rev = false) t = Ftree.enum ~rev t.rets
let dict t = t.dict
let start t = Pseudo_blk.label @@ Ftree.head_exn t.blks

let has_name t n = String.(n = t.name)

let linkage fn = match Dict.find fn.dict Virtual.Func.Tag.linkage with
  | None -> Linkage.default_export
  | Some l -> l

let map_of_blks t =
  Ftree.fold t.blks ~init:Label.Tree.empty ~f:(fun acc b ->
      Label.Tree.set acc ~key:b.label ~data:b)

let with_dict fn d = {
  fn with dict = d;
}

let with_blks fn bs = {
  fn with blks = Ftree.of_list bs;
}

let with_slots fn ss = {
  fn with slots = Ftree.of_list ss;
}

let insert_slot fn s = {
  fn with slots = Ftree.snoc fn.slots s;
}

let insert_slots fn = function
  | [] -> fn
  | ss -> {
      fn with slots = List.fold ss ~init:fn.slots ~f:Ftree.snoc;
    }

let map_blks fn ~f = {
  fn with blks = Ftree.map fn.blks ~f
}

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

let collect_afters fn =
  let rec aux acc s = match Seq.next s with
    | None -> acc
    | Some (x, xs) -> match Seq.next xs with
      | None -> acc
      | Some (y, _) ->
        let key = x.Pseudo_blk.label and data = y.label in
        aux (Label.Tree.set acc ~key ~data) xs in
  aux Label.Tree.empty @@ Ftree.enum fn.blks

let remove_blk_exn fn l =
  if Label.(l = entry fn)
  then invalid_argf "Cannot remove entry block of function $%s" fn.name ()
  else {fn with blks = Ftree.remove_if fn.blks ~f:(Fn.flip Pseudo_blk.has_label l)}

let remove_blks_exn fn = function
  | [] -> fn
  | [l] -> remove_blk_exn fn l
  | ls ->
    let s = Label.Tree_set.of_list ls in
    if Label.Tree_set.mem s @@ entry fn then
      invalid_argf "Cannot remove entry block of function $%s" fn.name ()
    else
      let f = Fn.non @@ Fn.compose (Label.Tree_set.mem s) Pseudo_blk.label in
      {fn with blks = Ftree.filter fn.blks ~f}

let pp ppa ppb ppf t =
  let sep_ret ppf = Format.fprintf ppf " " in
  let sep_blk ppf = Format.fprintf ppf "@;" in
  let lnk = linkage t in
  if Linkage.export lnk
  || Linkage.section lnk |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp lnk;
  Format.fprintf ppf "function $%s {" t.name;
  if not @@ Ftree.is_empty t.rets then
    Format.fprintf ppf " ; returns: %a"
      (Ftree.pp ppb sep_ret) t.rets;
  if not @@ Ftree.is_empty t.slots then begin
    let sep ppf = Format.fprintf ppf "@;  " in
    Format.fprintf ppf "@;@[<v 0>  %a@]"
      (Ftree.pp Slot.pp sep) t.slots
  end;
  if not @@ Ftree.is_empty t.blks then
    Format.fprintf ppf "@;@[<v 0>%a@]"
      (Ftree.pp (Pseudo_blk.pp ppa) sep_blk) t.blks;
  Format.fprintf ppf "@;}"
