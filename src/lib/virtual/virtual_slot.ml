open Core
open Regular.Std

module T = struct
  type t = {
    var   : Var.t;
    size  : int;
    align : int;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let create_exn x ~size ~align =
  if size < 0 then
    invalid_argf "Slot size for %a must be non-negative, got %d"
      Var.pps x size ();
  if align < 1 then
    invalid_argf "Slot alignment for %a must be greater than 0, got %d"
      Var.pps x align ();
  if (align land (align - 1)) <> 0 then
    invalid_argf "Slot alignment for %a must be a power of 2, got %d"
      Var.pps x align ();
  {var = x; size; align}

let create x ~size ~align = try Ok (create_exn x ~size ~align) with
  | Invalid_argument msg -> Or_error.error_string msg

let var t = t.var
let size t = t.size
let align t = t.align
let is_var t x = Var.(t.var = x)

let pp ppf t =
  Format.fprintf ppf "%a = slot %d, align %d"
    Var.pp t.var t.size t.align

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Slot"
    let version = "0.1"
    let pp = pp
  end)
