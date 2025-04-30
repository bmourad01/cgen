open Core
open Regular.Std
open Virtual_common

module Slot = Virtual_slot
module Func = Virtual_func
module Tag = Func.Tag

type arg = [
  | `reg of Var.t * string
  | `stk of Var.t * int
] [@@deriving bin_io, compare, equal, sexp]

let same_arg x y = match x, y with
  | `reg (x, _), `reg (y, _) -> Var.(x = y)
  | `stk (x, _), `stk (y, _) -> Var.(x = y)
  | _ -> false

let pp_arg ppf : arg -> unit = function
  | `reg (x, r) -> Format.fprintf ppf "%a/%s" Var.pp x r
  | `stk (x, s) -> Format.fprintf ppf "%a/+%d" Var.pp x s

module T = struct
  type t = {
    name  : string;
    slots : Slot.t ftree;
    blks  : Abi_blk.t ftree;
    args  : (arg * Type.basic) ftree;
    dict  : Dict.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

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
      slots = Ftree.of_list slots;
      blks = Ftree.of_list blks;
      args = Ftree.of_list args;
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
let slots ?(rev = false) fn = Ftree.enum fn.slots ~rev
let blks ?(rev = false) fn = Ftree.enum fn.blks ~rev
let entry fn = Abi_blk.label @@ Ftree.head_exn fn.blks
let args ?(rev = false) fn = Ftree.enum fn.args ~rev
let dict fn = fn.dict
let with_dict fn dict = {fn with dict}
let with_tag fn tag x = {fn with dict = Dict.set fn.dict tag x}
let variadic fn = Dict.mem fn.dict Func.Tag.variadic

let with_blks_exn fn = function
  | [] -> invalid_argf "Cannot create empty function $%s" fn.name ()
  | blks -> {fn with blks = Ftree.of_list blks}

let with_blks fn blks = try Ok (with_blks_exn fn blks) with
  | Invalid_argument msg -> Or_error.error_string msg

let linkage fn = match Dict.find fn.dict Func.Tag.linkage with
  | None -> Linkage.default_export
  | Some l -> l

let has_name fn name = String.(name = fn.name)
let hash fn = String.hash fn.name

let map_of_blks fn =
  Ftree.fold fn.blks ~init:Label.Tree.empty ~f:(fun m b ->
      let key = Abi_blk.label b in
      match Label.Tree.add m ~key ~data:b with
      | `Ok m -> m
      | `Duplicate ->
        invalid_argf
          "Duplicate block of label %a in function %s"
          Label.pps key fn.name ())

let map_blks fn ~f = {fn with blks = Ftree.map fn.blks ~f}

exception Failed of Error.t

let map_blks_err fn ~f = try
    let blks = Ftree.map fn.blks ~f:(fun b -> match f b with
        | Error e -> raise_notrace @@ Failed e
        | Ok b' -> b') in
    Ok {fn with blks}
  with Failed e -> Error e

let insert_blk fn b = {
  fn with blks = Ftree.snoc fn.blks b;
}

let insert_slot fn s = {
  fn with slots = Ftree.snoc fn.slots s;
}

let remove_blk_exn fn l =
  if Label.(l = entry fn)
  then invalid_argf "Cannot remove entry block of function $%s" fn.name ()
  else {fn with blks = Ftree.remove_if fn.blks ~f:(Fn.flip Abi_blk.has_label l)}

let remove_blks_exn fn = function
  | [] -> fn
  | [l] -> remove_blk_exn fn l
  | ls ->
    let s = Label.Tree_set.of_list ls in
    if Label.Tree_set.mem s @@ entry fn then
      invalid_argf "Cannot remove entry block of function $%s" fn.name ()
    else
      let f = Fn.non @@ Fn.compose (Label.Tree_set.mem s) Abi_blk.label in
      {fn with blks = Ftree.filter fn.blks ~f}

let remove_slot fn x = {
  fn with slots = Ftree.remove_if fn.slots ~f:(Fn.flip Slot.is_var x);
}

let is_arg (x, _) y = same_arg x y

let prepend_arg ?before fn x t = {
  fn with args = Ftree.icons ?before fn.args (x, t) is_arg;
}

let append_arg ?after fn x t = {
  fn with args = Ftree.isnoc ?after fn.args (x, t) is_arg;
}

let remove_arg fn x = {
  fn with args = Ftree.remove_if fn.args ~f:(Fn.flip is_arg x);
}

let remove_blk fn l = try Ok (remove_blk_exn fn l) with
  | Invalid_argument msg -> Or_error.error_string msg

let remove_blks fn ls = try Ok (remove_blks_exn fn ls) with
  | Invalid_argument msg -> Or_error.error_string msg

let has_blk fn l = Ftree.exists fn.blks ~f:(Fn.flip Abi_blk.has_label l)
let find_blk fn l = Ftree.find fn.blks ~f:(Fn.flip Abi_blk.has_label l)
let next_blk fn l = Ftree.next fn.blks ~f:(Fn.flip Abi_blk.has_label l)
let prev_blk fn l = Ftree.prev fn.blks ~f:(Fn.flip Abi_blk.has_label l)

let update_blk fn b =
  let l = Abi_blk.label b in {
    fn with blks = Ftree.update_if fn.blks b ~f:(Fn.flip Abi_blk.has_label l);
  }

let update_blks' fn m =
  if Label.Tree.is_empty m then fn
  else {
    fn with blks = Ftree.map fn.blks ~f:(fun b ->
      Abi_blk.label b |> Label.Tree.find m |> Option.value ~default:b);
  }

let update_blks_exn fn bs =
  update_blks' fn @@ List.fold bs
    ~init:Label.Tree.empty ~f:(fun m b ->
        let key = Abi_blk.label b in
        match Label.Tree.add m ~key ~data:b with
        | `Duplicate -> invalid_argf "Duplicate label %a" Label.pps key ()
        | `Ok m -> m)

let update_blks fn bs = try Ok (update_blks_exn fn bs) with
  | Invalid_argument msg -> Or_error.error_string msg

let pp_arg_ty ppf (v, t) =
  Format.fprintf ppf "%a %a" Type.pp_basic t pp_arg v

let pp_args ppf fn =
  let sep ppf = Format.fprintf ppf ", " in
  Format.fprintf ppf "%a" (Ftree.pp pp_arg_ty sep) fn.args;
  match Ftree.is_empty fn.args, variadic fn with
  | _,    false -> ()
  | true, true  -> Format.fprintf ppf "..."
  | _,    true  -> Format.fprintf ppf ", ..."

let pp ppf fn =
  let lnk = linkage fn in
  if Linkage.export lnk
  || Linkage.section lnk |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp lnk;
  Format.fprintf ppf "function ";
  Format.fprintf ppf "$%s(%a) {@;" fn.name pp_args fn;
  if not @@ Ftree.is_empty fn.slots then begin
    let sep ppf = Format.fprintf ppf "@;  " in
    Format.fprintf ppf "@[<v 0>  %a@]@;" (Ftree.pp Slot.pp sep) fn.slots
  end;
  let sep ppf = Format.fprintf ppf "@;" in
  Format.fprintf ppf "@[<v 0>%a@]@;}"(Ftree.pp Abi_blk.pp sep) fn.blks

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Abi.Fn"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
