open Core
open Regular.Std
open Common

module Slot = struct
  type t = {
    var   : Var.t;
    size  : int;
    align : int;
  } [@@deriving bin_io, compare, equal, sexp]

  let create_exn x ~size ~align =
    if size < 1 then
      invalid_argf "Slot size for %a must be greater than 0, got %d"
        Var.pps x size ();
    if align < 1 then
      invalid_argf "Slot alignment for %a must be greater than 0, got %d"
        Var.pps x align ();
    if (align land (align - 1)) <> 0 then
      invalid_argf "Slot alignment for %a must be a power of 2, got %d"
        Var.pps x align ();
    {var = x; size; align}

  let create x ~size ~align =
    Or_error.try_with @@ fun () -> create_exn x ~size ~align

  let var t = t.var
  let size t = t.size
  let align t = t.align
  let is_var t x = Var.(t.var = x)

  let pp ppf t =
    Format.fprintf ppf "%a = slot %d, align %d"
      Var.pp t.var t.size t.align
end

type slot = Slot.t [@@deriving bin_io, compare, equal, sexp]

let pp_slot = Slot.pp

module T = struct
  type t = {
    name     : string;
    slots    : slot ftree;
    blks     : Blk.t ftree;
    entry    : Label.t;
    args     : (Var.t * Type.arg) ftree;
    return   : Type.basic option;
    variadic : bool;
    noreturn : bool;
    linkage  : Linkage.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create_exn
    ?(slots = [])
    ?(return = None)
    ?(variadic = false)
    ?(noreturn = false)
    ?(linkage = Linkage.default_export)
    ~name
    ~blks
    ~args
    () = match blks with
  | [] -> invalid_argf "Cannot create empty function %s" name ()
  | {Blk.label = entry; _} :: _ -> {
      name;
      slots = Ftree.of_list slots;
      blks = Ftree.of_list blks;
      entry;
      args = Ftree.of_list args;
      return;
      variadic;
      noreturn;
      linkage;
    }

let create
    ?(slots = [])
    ?(return = None)
    ?(variadic = false)
    ?(noreturn = false)
    ?(linkage = Linkage.default_export)
    ~name
    ~blks
    ~args
    () =
  Or_error.try_with @@
  create_exn ~name ~blks ~args
    ~slots ~return ~variadic
    ~noreturn ~linkage

let name fn = fn.name
let slots ?(rev = false) fn = Ftree.enum fn.slots ~rev
let blks ?(rev = false) fn = Ftree.enum fn.blks ~rev
let entry fn = fn.entry
let args ?(rev = false) fn = Ftree.enum fn.args ~rev
let return fn = fn.return
let variadic fn = fn.variadic
let noreturn fn = fn.noreturn
let linkage fn = fn.linkage
let has_name fn name = String.(name = fn.name)
let hash fn = String.hash fn.name

exception Failed of Error.t

let typeof fn =
  let args = Ftree.enum fn.args |> Seq.map ~f:snd |> Seq.to_list in
  `proto (fn.return, args, fn.variadic)

let map_of_blks fn =
  Ftree.fold fn.blks ~init:Label.Tree.empty ~f:(fun m b ->
      let key = Blk.label b in
      match Label.Tree.add m ~key ~data:b with
      | `Ok m -> m
      | `Duplicate ->
        invalid_argf
          "Duplicate block of label %a in function %s"
          Label.pps key fn.name ())

let map_blks fn ~f =
  let entry = ref fn.entry in
  let is_entry b = Label.(Blk.label b = fn.entry) in
  let blks = Ftree.map fn.blks ~f:(fun b ->
      let b' = f b in
      if is_entry b then entry := Blk.label b';
      b') in
  {fn with blks; entry = !entry}

let map_blks_err fn ~f = try
    let entry = ref fn.entry in
    let is_entry b = Label.(Blk.label b = fn.entry) in
    let blks = Ftree.map fn.blks ~f:(fun b ->
        let b' = match f b with
          | Error e -> raise @@ Failed e
          | Ok b' -> b' in
        if is_entry b then entry := Blk.label b';
        b') in
    Ok {fn with blks; entry = !entry}
  with Failed e -> Error e

let insert_blk fn b = {
  fn with blks = Ftree.snoc fn.blks b;
}

let insert_slot fn s = {
  fn with slots = Ftree.snoc fn.slots s;
}

let remove_blk_exn fn l =
  if Label.(l = fn.entry)
  then invalid_argf "Cannot remove entry block of function $%s" fn.name ()
  else {fn with blks = Ftree.remove_if fn.blks ~f:(Fn.flip Blk.has_label l)}

let remove_slot fn x = {
  fn with slots = Ftree.remove_if fn.slots ~f:(Fn.flip Slot.is_var x);
}  

let remove_blk fn l = Or_error.try_with @@ fun () -> remove_blk_exn fn l
let has_blk fn l = Ftree.exists fn.blks ~f:(Fn.flip Blk.has_label l)
let find_blk fn l = Ftree.find fn.blks ~f:(Fn.flip Blk.has_label l)
let next_blk fn l = Ftree.next fn.blks ~f:(Fn.flip Blk.has_label l)
let prev_blk fn l = Ftree.prev fn.blks ~f:(Fn.flip Blk.has_label l)

let update_blk fn b =
  let l = Blk.label b in {
    fn with blks = Ftree.update_if fn.blks b ~f:(Fn.flip Blk.has_label l);
  }

let update_blks fn = function
  | [] -> fn
  | bs ->
    let m = List.fold bs ~init:Label.Tree.empty ~f:(fun m b ->
        let key = Blk.label b in
        match Label.Tree.add m ~key ~data:b with
        | `Duplicate -> invalid_argf "Duplicate label %a" Label.pps key ()
        | `Ok m -> m) in {
      fn with blks = Ftree.map fn.blks ~f:(fun b ->
        Blk.label b |> Label.Tree.find m |> Option.value ~default:b);
    }

let pp_arg ppf (v, t) = Format.fprintf ppf "%a %a" Type.pp_arg t Var.pp v

let pp_args ppf fn =
  let sep ppf = Format.fprintf ppf ", " in
  Format.fprintf ppf "%a" (Ftree.pp pp_arg sep) fn.args;
  match Ftree.is_empty fn.args, fn.variadic with
  | _,    false -> ()
  | true, true  -> Format.fprintf ppf "..."
  | _,    true  -> Format.fprintf ppf ", ..."

let pp ppf fn =
  if Linkage.export fn.linkage
  || Linkage.section fn.linkage |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp fn.linkage;
  if fn.noreturn then Format.fprintf ppf "noreturn ";
  Format.fprintf ppf "function ";
  Option.iter fn.return ~f:(Format.fprintf ppf "%a " Type.pp_basic);
  Format.fprintf ppf "$%s(%a) {@;" fn.name pp_args fn;
  if not @@ Ftree.is_empty fn.slots then begin
    let sep ppf = Format.fprintf ppf "@;  " in
    Format.fprintf ppf "@[<v 0>  %a@]@;" (Ftree.pp pp_slot sep) fn.slots
  end;
  let sep ppf = Format.fprintf ppf "@;" in
  Format.fprintf ppf "@[<v 0>%a@]@;}"(Ftree.pp Blk.pp sep) fn.blks

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Fn"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
