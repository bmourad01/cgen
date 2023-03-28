open Core
open Regular.Std
open Common

module T = struct
  type t = {
    name     : string;
    blks     : Blk.t array;
    entry    : Label.t;
    args     : (Var.t * Type.arg) array;
    return   : Type.basic option;
    variadic : bool;
    noreturn : bool;
    linkage  : Linkage.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create_exn
    ?(return = None)
    ?(variadic = false)
    ?(noreturn = false)
    ?(linkage = Linkage.default_export)
    ~name
    ~blks
    ~args
    () = match Array.of_list blks with
  | [||] -> invalid_argf "Cannot create empty function %s" name ()
  | blks -> {
      name;
      blks;
      entry = blks.(0).label;
      args = Array.of_list args;
      return;
      variadic;
      noreturn;
      linkage;
    }

let create
    ?(return = None)
    ?(variadic = false)
    ?(noreturn = false)
    ?(linkage = Linkage.default_export)
    ~name
    ~blks
    ~args
    () =
  Or_error.try_with @@
  create_exn ~name ~blks ~args ~return ~variadic ~noreturn ~linkage

let name fn = fn.name
let blks ?(rev = false) fn = Array.enum fn.blks ~rev
let entry fn = fn.entry
let args ?(rev = false) fn = Array.enum fn.args ~rev
let return fn = fn.return
let variadic fn = fn.variadic
let noreturn fn = fn.noreturn
let linkage fn = fn.linkage
let has_name fn name = String.(name = fn.name)
let hash fn = String.hash fn.name

let typeof fn =
  let args = Array.enum fn.args |> Seq.map ~f:snd |> Seq.to_list in
  `proto (fn.return, args, fn.variadic)

let map_of_blks fn =
  Array.fold fn.blks ~init:Label.Map.empty ~f:(fun m b ->
      let key = Blk.label b in
      match Map.add m ~key ~data:b with
      | `Ok m -> m
      | `Duplicate ->
        invalid_argf
          "Duplicate block of label %a in function %s"
          Label.pps key fn.name ())

let map_blks fn ~f =
  let entry = ref fn.entry in
  let is_entry b = Label.(Blk.label b = fn.entry) in
  let blks = Array.map fn.blks ~f:(fun b ->
      let b' = f b in
      if is_entry b then entry := Blk.label b';
      b') in
  {fn with blks; entry = !entry}

let insert_blk fn b = {
  fn with blks = Array.push_back fn.blks b;
}

let remove_blk_exn fn l =
  if Label.(l = fn.entry)
  then invalid_argf "Cannot remove entry block of function $%s" fn.name ()
  else {fn with blks = Array.remove_if fn.blks ~f:(Fn.flip Blk.has_label l)}

let remove_blk fn l = Or_error.try_with @@ fun () -> remove_blk_exn fn l
let has_blk fn l = Array.exists fn.blks ~f:(Fn.flip Blk.has_label l)
let find_blk fn l = Array.find fn.blks ~f:(Fn.flip Blk.has_label l)
let next_blk fn l = Array.next fn.blks Blk.label l
let prev_blk fn l = Array.prev fn.blks Blk.label l

let update_blk fn b =
  let l = Blk.label b in {
    fn with blks = Array.update_if fn.blks b ~f:(Fn.flip Blk.has_label l);
  }

let pp_arg ppf (v, t) = Format.fprintf ppf "%a %a" Type.pp_arg t Var.pp v

let pp_args ppf fn =
  let sep ppf = Format.fprintf ppf ", " in
  Format.fprintf ppf "%a" (Array.pp pp_arg sep) fn.args;
  match fn.args, fn.variadic with
  | _, false -> ()
  | [||], true -> Format.fprintf ppf "..."
  | _, true -> Format.fprintf ppf ", ..."

let pp ppf fn =
  let sep ppf = Format.fprintf ppf "@;" in
  if Linkage.export fn.linkage
  || Linkage.section fn.linkage |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp fn.linkage;
  if fn.noreturn then Format.fprintf ppf "noreturn ";
  Format.fprintf ppf "function ";
  Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp_basic);
  Format.fprintf ppf "$%s(%a) {@;@[<v 0>%a@]@;}"
    fn.name pp_args fn (Array.pp Blk.pp sep) fn.blks

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Fn"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)

