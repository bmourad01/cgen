open Core
open Regular.Std
open Common

module T = struct
  type t = [
    | `always
    | `true_ of Var.t
    | `false_ of Var.t
    | `switch of Ctrl.swindex * Bitvec.t
    | `default of Ctrl.swindex
  ] [@@deriving bin_io, compare, equal, sexp]
end

include T

let pp ppf : t -> unit = function
  | `always ->
    Format.fprintf ppf "always"
  | `true_ x ->
    Format.fprintf ppf "%a" Var.pp x
  | `false_ x ->
    Format.fprintf ppf "~%a" Var.pp x
  | `switch (x, v) ->
    Format.fprintf ppf "%a = %a" Ctrl.pp_swindex x Bitvec.pp v
  | `default x ->
    Format.fprintf ppf "default(%a)" Ctrl.pp_swindex x

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Edge"
    let version = "0.1"
    let pp = pp
    let hash e = String.hash @@ Format.asprintf "%a" pp e
  end)
