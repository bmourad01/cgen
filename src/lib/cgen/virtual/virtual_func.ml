open Core
open Cgen_containers

module Regular = Cgen_utils.Regular
module Blk = Virtual_blk
module Slot = Virtual_slot

module T = struct
  type t = {
    name  : string;
    slots : Slot.t Rrb.t;
    blks  : Blk.t Rrb.t;
    args  : (Var.t * Type.arg) Rrb.t;
    dict  : Dict.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

module Tag = struct
  let return = Dict.register "fn-return" (module struct
      type t = Type.ret [@@deriving bin_io, compare, equal, sexp]
      let pp = Type.pp_ret
    end)

  let variadic = Dict.register "fn-variadic" (module Unit)

  let noreturn = Dict.register "fn-noreturn" (module Unit)

  let linkage = Dict.register "fn-linkage" (module Linkage)
end

let create_exn
    ?(dict = Dict.empty)
    ?(slots = [])
    ~name
    ~blks
    ~args
    () = match blks with
  | [] -> invalid_argf "Cannot create empty function $%s" name ()
  | _ :: _ -> {
      name;
      slots = Rrb.of_list slots;
      blks = Rrb.of_list blks;
      args = Rrb.of_list args;
      dict;
    }

let create
    ?(dict = Dict.empty)
    ?(slots = [])
    ~name
    ~blks
    ~args
    () = try Ok (create_exn () ~name ~blks ~args ~slots ~dict) with
  | Invalid_argument msg -> Or_error.error_string msg

let name fn = fn.name

let slots ?(rev = false) fn =
  if rev then Rrb.to_sequence_rev fn.slots else Rrb.to_sequence fn.slots

let has_any_slots fn = not (Rrb.is_empty fn.slots)
let num_slots fn = Rrb.length fn.slots

let fold_slots ?(rev = false) fn ~init ~f =
  if rev then Rrb.fold_right fn.slots ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold fn.slots ~init ~f

let iter_slots ?(rev = false) fn ~f =
  if rev then Rrb.iter_rev fn.slots ~f
  else Rrb.iter fn.slots ~f

let blks ?(rev = false) fn =
  if rev then Rrb.to_sequence_rev fn.blks else Rrb.to_sequence fn.blks

let num_blks fn = Rrb.length fn.blks

let fold_blks ?(rev = false) fn ~init ~f =
  if rev then Rrb.fold_right fn.blks ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold fn.blks ~init ~f

let iter_blks ?(rev = false) fn ~f =
  if rev then Rrb.iter_rev fn.blks ~f
  else Rrb.iter fn.blks ~f

let num_insns fn =
  fold_blks fn ~init:0 ~f:(fun acc b ->
      acc + Virtual_blk.num_insns b)

let entry fn = Blk.label @@ Rrb.get_exn fn.blks 0

let args ?(rev = false) fn =
  if rev then Rrb.to_sequence_rev fn.args else Rrb.to_sequence fn.args

let has_any_args fn = not (Rrb.is_empty fn.args)
let num_args fn = Rrb.length fn.args

let iter_args ?(rev = false) fn ~f =
  if rev then Rrb.iter_rev fn.args ~f
  else Rrb.iter fn.args ~f

let fold_args ?(rev = false) fn ~init ~f =
  if rev then Rrb.fold_right fn.args ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold fn.args ~init ~f

let return fn = Dict.find fn.dict Tag.return
let variadic fn = Dict.mem fn.dict Tag.variadic
let noreturn fn = Dict.mem fn.dict Tag.noreturn
let dict fn = fn.dict
let with_dict fn dict = {fn with dict}
let with_tag fn tag x = {fn with dict = Dict.set fn.dict tag x}

let with_blks_exn fn = function
  | [] -> invalid_argf "Cannot create empty function $%s" fn.name ()
  | blks -> {fn with blks = Rrb.of_list blks}

let with_blks fn blks = try Ok (with_blks_exn fn blks) with
  | Invalid_argument msg -> Or_error.error_string msg

let linkage fn = match Dict.find fn.dict Tag.linkage with
  | None -> Linkage.default_static
  | Some l -> l

let has_name fn name = String.(name = fn.name)
let hash fn = String.hash fn.name

let typeof fn =
  let args = Rrb.to_sequence fn.args |> Sequence.map ~f:snd |> Sequence.to_list in
  `proto (return fn, args, variadic fn)

let map_of_blks fn =
  Rrb.fold fn.blks ~init:Label.Tree.empty ~f:(fun m b ->
      let key = Blk.label b in
      match Label.Tree.add m ~key ~data:b with
      | `Ok m -> m
      | `Duplicate ->
        invalid_argf
          "Duplicate block of label %a in function %s"
          Label.pps key fn.name ())

let fold_reachable fn ~init ~f =
  let index = map_of_blks fn in
  let nblk = Rrb.length fn.blks in
  let visited = Label.Dense_set.create ~capacity:nblk () in
  let rec go acc = function
    | [] -> acc
    | l :: rest ->
      if Label.Dense_set.strict_add visited l then
        match Label.Tree.find index l with
        | None -> go acc rest
        | Some b ->
          let c = Blk.ctrl b in
          let rest =
            Virtual_ctrl.fold_dests c ~init:rest
              ~f:(fun stk l -> l :: stk) in
          go (f acc b) rest
      else go acc rest in
  go init [entry fn]

let iter_reachable fn ~f =
  fold_reachable fn ~init:() ~f:(fun () b -> f b)

let map_blks fn ~f = {fn with blks = Rrb.map fn.blks ~f}

exception Failed of Error.t

let map_blks_err fn ~f = try
    let blks = Rrb.map fn.blks ~f:(fun b -> match f b with
        | Error e -> raise_notrace @@ Failed e
        | Ok b' -> b') in
    Ok {fn with blks}
  with Failed e -> Error e

let filter_map_blks_exn fn ~f =
  let blks = Rrb.filter_map fn.blks ~f in
  if Rrb.is_empty blks
  then invalid_argf "Cannot create empty function $%s" fn.name ()
  else {fn with blks}

let filter_map_blks fn ~f = try Ok (filter_map_blks_exn fn ~f) with
  | Invalid_argument msg -> Or_error.error_string msg

let insert_blk fn b = {
  fn with blks = Rrb.snoc fn.blks b;
}

let insert_slot fn s = {
  fn with slots = Rrb.snoc fn.slots s;
}

let remove_blk_exn fn l =
  if Label.(l = entry fn)
  then invalid_argf "Cannot remove entry block of function $%s" fn.name ()
  else {fn with blks = Rrb.filter fn.blks ~f:(fun b -> not @@ Blk.has_label b l)}

let remove_blks_exn fn = function
  | [] -> fn
  | [l] -> remove_blk_exn fn l
  | ls ->
    let s = Label.Tree_set.of_list ls in
    if Label.Tree_set.mem s @@ entry fn then
      invalid_argf "Cannot remove entry block of function $%s" fn.name ()
    else
      let f = Fn.non @@ Fn.compose (Label.Tree_set.mem s) Blk.label in
      {fn with blks = Rrb.filter fn.blks ~f}

let remove_slot fn x = {
  fn with slots = Rrb.filter fn.slots ~f:(fun s -> not @@ Slot.is_var s x);
}

let is_arg (x, _) y = Var.(x = y)

let prepend_arg ?before fn x t =
  let args = match before with
    | None -> Rrb.cons (x, t) fn.args
    | Some k -> Rrb.insert_before fn.args (Rrb.singleton (x, t)) ~f:(fun a -> is_arg a k) in
  {fn with args}

let append_arg ?after fn x t =
  let args = match after with
    | None -> Rrb.snoc fn.args (x, t)
    | Some k -> Rrb.insert_after fn.args (Rrb.singleton (x, t)) ~f:(fun a -> is_arg a k) in
  {fn with args}

let remove_arg fn x = {
  fn with args = Rrb.filter fn.args ~f:(fun a -> not @@ is_arg a x);
}

let remove_blk fn l = try Ok (remove_blk_exn fn l) with
  | Invalid_argument msg -> Or_error.error_string msg

let remove_blks fn ls = try Ok (remove_blks_exn fn ls) with
  | Invalid_argument msg -> Or_error.error_string msg

let has_blk fn l = Rrb.exists fn.blks ~f:(fun b -> Blk.has_label b l)
let find_blk fn l = Rrb.find fn.blks ~f:(fun b -> Blk.has_label b l)

let next_blk fn l =
  match Rrb.find_index fn.blks ~f:(fun b -> Blk.has_label b l) with
  | Some i -> Rrb.get fn.blks (i + 1)
  | None -> None

let prev_blk fn l =
  match Rrb.find_index fn.blks ~f:(fun b -> Blk.has_label b l) with
  | Some i when i > 0 -> Some (Rrb.get_exn fn.blks (i - 1))
  | Some _ | None -> None

let update_blk fn b =
  let l = Blk.label b in
  match Rrb.find_index fn.blks ~f:(fun b' -> Blk.has_label b' l) with
  | Some i -> {fn with blks = Rrb.set fn.blks i b}
  | None -> fn

let update_blks' fn m =
  if Label.Tree.is_empty m then fn
  else {
    fn with blks = Rrb.map fn.blks ~f:(fun b ->
      Blk.label b |> Label.Tree.find m |> Option.value ~default:b);
  }

let update_blks_exn fn bs =
  update_blks' fn @@ List.fold bs
    ~init:Label.Tree.empty ~f:(fun m b ->
        let key = Blk.label b in
        match Label.Tree.add m ~key ~data:b with
        | `Duplicate -> invalid_argf "Duplicate label %a" Label.pps key ()
        | `Ok m -> m)

let update_blks fn bs = try Ok (update_blks_exn fn bs) with
  | Invalid_argument msg -> Or_error.error_string msg

let pp_rrb pp_elt sep ppf t =
  let first = ref true in
  Rrb.iter t ~f:(fun x ->
      if !first then first := false else sep ppf;
      pp_elt ppf x)

let pp_arg ppf (v, t) = Format.fprintf ppf "%a %a" Type.pp_arg t Var.pp v

let pp_args ppf fn =
  let sep ppf = Format.fprintf ppf ", " in
  pp_rrb pp_arg sep ppf fn.args;
  match Rrb.is_empty fn.args, variadic fn with
  | _,    false -> ()
  | true, true  -> Format.fprintf ppf "..."
  | _,    true  -> Format.fprintf ppf ", ..."

let pp ppf fn =
  let lnk = linkage fn in
  if Linkage.export lnk
  || Linkage.section lnk |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp lnk;
  if noreturn fn then Format.fprintf ppf "noreturn ";
  Format.fprintf ppf "function ";
  Option.iter (return fn) ~f:(Format.fprintf ppf "%a " Type.pp_ret);
  Format.fprintf ppf "$%s(%a) {@;" fn.name pp_args fn;
  if not @@ Rrb.is_empty fn.slots then begin
    let sep ppf = Format.fprintf ppf "@;  " in
    Format.fprintf ppf "@[<v 0>  %a@]@;" (pp_rrb Slot.pp sep) fn.slots
  end;
  let sep ppf = Format.fprintf ppf "@;" in
  Format.fprintf ppf "@[<v 0>%a@]@;}" (pp_rrb Blk.pp sep) fn.blks

include Regular.Make(struct
    include T
    let pp = pp
    let hash = hash
  end)
