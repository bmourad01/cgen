open Core
open Cgen_containers

module Slot = Virtual.Slot

type ('a, 'b) t = {
  name  : string;
  slots : Slot.t Rrb.t;
  blks  : 'a Pseudo_blk.t Rrb.t;
  rets  : 'b Rrb.t;
  dict  : Dict.t;
} [@@deriving bin_io, compare, equal, sexp]

let entry t = (Rrb.get_exn t.blks 0).label

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
      slots = Rrb.of_list slots;
      blks = Rrb.of_list blks;
      rets = Rrb.of_list rets;
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

let slots ?(rev = false) t =
  if rev then Rrb.to_sequence_rev t.slots else Rrb.to_sequence t.slots

let has_any_slots t = not (Rrb.is_empty t.slots)
let num_slots t = Rrb.length t.slots

let fold_slots ?(rev = false) t ~init ~f =
  if rev then Rrb.fold_right t.slots ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold t.slots ~init ~f

let iter_slots ?(rev = false) t ~f =
  if rev then Rrb.iter_rev t.slots ~f
  else Rrb.iter t.slots ~f

let blks ?(rev = false) t =
  if rev then Rrb.to_sequence_rev t.blks else Rrb.to_sequence t.blks

let num_blks t = Rrb.length t.blks

let fold_blks ?(rev = false) t ~init ~f =
  if rev then Rrb.fold_right t.blks ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold t.blks ~init ~f

let iter_blks ?(rev = false) t ~f =
  if rev then Rrb.iter_rev t.blks ~f
  else Rrb.iter t.blks ~f

let num_insns t =
  fold_blks t ~init:0 ~f:(fun acc b ->
      acc + Pseudo_blk.num_insns b)

let rets ?(rev = false) t =
  if rev then Rrb.to_sequence_rev t.rets else Rrb.to_sequence t.rets

let fold_rets ?(rev = false) t ~init ~f =
  if rev then Rrb.fold_right t.rets ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold t.rets ~init ~f

let dict t = t.dict
let start t = Pseudo_blk.label @@ Rrb.get_exn t.blks 0

let has_name t n = String.(n = t.name)

let linkage fn = match Dict.find fn.dict Virtual.Func.Tag.linkage with
  | None -> Linkage.default_export
  | Some l -> l

let map_of_blks t =
  Rrb.fold t.blks ~init:Label.Tree.empty ~f:(fun acc b ->
      Label.Tree.set acc ~key:b.label ~data:b)

let with_dict fn d = {
  fn with dict = d;
}

let with_blks fn bs = {
  fn with blks = Rrb.of_list bs;
}

let with_slots fn ss = {
  fn with slots = Rrb.of_list ss;
}

let insert_slot fn s = {
  fn with slots = Rrb.snoc fn.slots s;
}

let insert_slots fn = function
  | [] -> fn
  | ss -> {
      fn with slots = List.fold ss ~init:fn.slots ~f:Rrb.snoc;
    }

let map_blks fn ~f = {
  fn with blks = Rrb.map fn.blks ~f
}

let update_blk fn b =
  let l = Pseudo_blk.label b in
  match Rrb.find_index fn.blks ~f:(fun b' -> Pseudo_blk.has_label b' l) with
  | Some i -> {fn with blks = Rrb.set fn.blks i b}
  | None -> fn

let update_blks' t blks =
  let blks = Rrb.map t.blks ~f:(fun b ->
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
  let rec aux acc s = match Sequence.next s with
    | None -> acc
    | Some (x, xs) -> match Sequence.next xs with
      | None -> acc
      | Some (y, _) ->
        let key = x.Pseudo_blk.label and data = y.label in
        aux (Label.Tree.set acc ~key ~data) xs in
  aux Label.Tree.empty @@ Rrb.to_sequence fn.blks

let remove_blk_exn fn l =
  if Label.(l = entry fn)
  then invalid_argf "Cannot remove entry block of function $%s" fn.name ()
  else {fn with blks = Rrb.filter fn.blks ~f:(fun b -> not @@ Pseudo_blk.has_label b l)}

let remove_blks_exn fn = function
  | [] -> fn
  | [l] -> remove_blk_exn fn l
  | ls ->
    let s = Label.Tree_set.of_list ls in
    if Label.Tree_set.mem s @@ entry fn then
      invalid_argf "Cannot remove entry block of function $%s" fn.name ()
    else
      let f = Fn.non @@ Fn.compose (Label.Tree_set.mem s) Pseudo_blk.label in
      {fn with blks = Rrb.filter fn.blks ~f}

let filter_map_blks fn ~f = {fn with blks = Rrb.filter_map fn.blks ~f}

let pp_rrb pp_elt sep ppf t =
  let first = ref true in
  Rrb.iter t ~f:(fun x ->
      if !first then first := false else sep ppf;
      pp_elt ppf x)

let pp ppa ppb ppf t =
  let sep_ret ppf = Format.fprintf ppf " " in
  let sep_blk ppf = Format.fprintf ppf "@;" in
  let lnk = linkage t in
  if Linkage.export lnk
  || Linkage.section lnk |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp lnk;
  Format.fprintf ppf "function $%s {" t.name;
  if not @@ Rrb.is_empty t.rets then
    Format.fprintf ppf " ; returns: %a"
      (pp_rrb ppb sep_ret) t.rets;
  if not @@ Rrb.is_empty t.slots then begin
    let sep ppf = Format.fprintf ppf "@;  " in
    Format.fprintf ppf "@;@[<v 0>  %a@]"
      (pp_rrb Slot.pp sep) t.slots
  end;
  if not @@ Rrb.is_empty t.blks then
    Format.fprintf ppf "@;@[<v 0>%a@]"
      (pp_rrb (Pseudo_blk.pp ppa) sep_blk) t.blks;
  Format.fprintf ppf "@;}"
