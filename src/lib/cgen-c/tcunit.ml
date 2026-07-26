open Core

type t = {
  decls  : Tdecl.t list;
  layout : Type_env.t;
} [@@deriving bin_io, compare, equal, hash, sexp]

let create ~decls ~layout = {decls; layout}

let decls t = t.decls
let layout t = t.layout
let tenv t = t.layout
let dmodel t = Type_env.dmodel t.layout

(* Pretty printing. *)

let pp ppf {decls; _} =
  Format.fprintf ppf "@[<v 0>";
  List.iteri decls ~f:(fun i d ->
      if i > 0 then Format.fprintf ppf "@,@,";
      Tdecl.pp ppf d);
  Format.fprintf ppf "@]"

let to_string u = Format.asprintf "%a" pp u
