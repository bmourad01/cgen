open Core
module Regular = Cgen_utils.Regular
open Cgen_containers

module T = struct
  type t = {
    name  : string;
    slots : Virtual.Slot.t Rrb.t;
    args  : (Var.t * Type.arg) Rrb.t;
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
  slots = Rrb.of_list slots;
  args = Rrb.of_list args;
  body;
  dict;
}

let name fn = fn.name

let slots ?(rev = false) fn =
  if rev then Rrb.to_sequence_rev fn.slots else Rrb.to_sequence fn.slots

let body fn = fn.body

let args ?(rev = false) fn =
  if rev then Rrb.to_sequence_rev fn.args else Rrb.to_sequence fn.args

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
  let args = Rrb.to_sequence fn.args |> Sequence.map ~f:snd |> Sequence.to_list in
  `proto (return fn, args, variadic fn)

let map_body fn ~f = {fn with body = f fn.body}

let insert_slot fn s = {
  fn with slots = Rrb.snoc fn.slots s;
}

let remove_slot fn x = {
  fn with slots = Rrb.filter fn.slots ~f:(fun s -> not @@ Virtual.Slot.is_var s x);
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

let pp_arg ppf (v, t) = Format.fprintf ppf "%a %a" Type.pp_arg t Var.pp v

let pp_rrb pp_elt sep ppf t =
  let first = ref true in
  Rrb.iter t ~f:(fun x ->
      if !first then first := false else sep ppf;
      pp_elt ppf x)

let pp_args ppf fn =
  let sep ppf = Format.fprintf ppf ", " in
  Format.fprintf ppf "%a" (pp_rrb pp_arg sep) fn.args;
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
    Format.fprintf ppf "@[<v 0>  %a@]@;" (pp_rrb Virtual.Slot.pp sep) fn.slots
  end;
  Format.fprintf ppf "@[<v 0>start:@;@[<v 2>  %a@]@]@;}" Structured_stmt.pp fn.body

include Regular.Make(struct
    include T
    let pp = pp
    let hash = hash
  end)
