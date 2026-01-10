open Core
open Regular.Std
open Structured_common

module T = struct
  type t = {
    name  : string;
    slots : Virtual.Slot.t ftree;
    args  : (Var.t * Type.arg) ftree;
    body  : Structured_stmt.t;
    dict  : Dict.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

module Tag = Virtual.Func.Tag

let create
    ?(dict = Dict.empty)
    ?(slots = [])
    ~name
    ~body
    ~args
    () = {
  name;
  slots = Ftree.of_list slots;
  args = Ftree.of_list args;
  body;
  dict;
}

let name fn = fn.name
let slots ?(rev = false) fn = Ftree.enum fn.slots ~rev
let body fn = fn.body
let args ?(rev = false) fn = Ftree.enum fn.args ~rev
let return fn = Dict.find fn.dict Tag.return
let variadic fn = Dict.mem fn.dict Tag.variadic
let noreturn fn = Dict.mem fn.dict Tag.noreturn
let dict fn = fn.dict
let with_dict fn dict = {fn with dict}
let with_tag fn tag x = {fn with dict = Dict.set fn.dict tag x}
let with_body fn body = {fn with body}
let has_name fn name = String.(name = fn.name)
let hash fn = String.hash fn.name

let linkage fn = match Dict.find fn.dict Tag.linkage with
  | None -> Linkage.default_static
  | Some l -> l

let typeof fn =
  let args = Ftree.enum fn.args |> Seq.map ~f:snd |> Seq.to_list in
  `proto (return fn, args, variadic fn)

let map_body fn ~f = {fn with body = f fn.body}

let insert_slot fn s = {
  fn with slots = Ftree.snoc fn.slots s;
}

let remove_slot fn x = {
  fn with slots = Ftree.remove_if fn.slots ~f:(Fn.flip Virtual.Slot.is_var x);
}  

let is_arg (x, _) y = Var.(x = y)

let prepend_arg ?before fn x t = {
  fn with args = Ftree.icons ?before fn.args (x, t) is_arg;
}

let append_arg ?after fn x t = {
  fn with args = Ftree.isnoc ?after fn.args (x, t) is_arg;
}

let remove_arg fn x = {
  fn with args = Ftree.remove_if fn.args ~f:(Fn.flip is_arg x);
}

let pp_arg ppf (v, t) = Format.fprintf ppf "%a %a" Type.pp_arg t Var.pp v

let pp_args ppf fn =
  let sep ppf = Format.fprintf ppf ", " in
  Format.fprintf ppf "%a" (Ftree.pp pp_arg sep) fn.args;
  match Ftree.is_empty fn.args, variadic fn with
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
  if not @@ Ftree.is_empty fn.slots then begin
    let sep ppf = Format.fprintf ppf "@;  " in
    Format.fprintf ppf "@[<v 0>  %a@]@;" (Ftree.pp Virtual.Slot.pp sep) fn.slots
  end;
  Format.fprintf ppf "@[<v 0>start:@;@[<v 2>  %a@]@]@;}" Structured_stmt.pp fn.body

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Structured.Func"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
