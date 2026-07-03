open Core

type 'a t = {
  decls : 'a Decl.t list;
} [@@deriving bin_io, compare, equal, hash, sexp]

let create decls = {decls}

let decls t = t.decls

(* Pretty printing. *)

let pp ppf {decls} =
  Format.fprintf ppf "@[<v 0>";
  List.iteri decls ~f:(fun i d ->
      if i > 0 then Format.fprintf ppf "@,@,";
      Decl.pp ppf d);
  Format.fprintf ppf "@]"

let to_string u = Format.asprintf "%a" pp u
