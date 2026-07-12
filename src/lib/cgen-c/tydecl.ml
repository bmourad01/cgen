open Core

(* Type declarations: the struct/union/enum/typedef definitions a
   declaration specifier can introduce. Factored out of `Decl` (which also
   carries function definitions, and so depends on `Stmt`) so that `Stmt` can
   carry them for block-scope declarations without a cyclic dependency; these
   forms depend only on `Expr`/`Type`/`Attr`. *)

type 'a field = {
  fname  : string;
  fty    : 'a Expr.ty;
  fbits  : 'a Expr.t option;
  fattrs : 'a Attr.raws;
} [@@deriving bin_io, compare, equal, hash, sexp]

type 'a eitem = {
  einame  : string;
  eivalue : 'a Expr.t option;
} [@@deriving bin_io, compare, equal, hash, sexp]

type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Compound of {
      kind   : Type.compound;
      tag    : string;
      fields : 'a field list option;
      attrs  : 'a Attr.raws;
    }
  | Enum of {
      tag   : string;
      items : 'a eitem list;
    }
  | Typedef of {
      name : string;
      ty   : 'a Expr.ty;
    }
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors. *)

let compound ?(attrs = []) ~kind ~tag ~fields ~ann () =
  {node = Compound {kind; tag; fields; attrs}; ann}

let enum ~tag ~items ~ann = {node = Enum {tag; items}; ann}

let typedef ~name ~ty ~ann = {node = Typedef {name; ty}; ann}

let field ?bits ?(attrs = []) ~name ~ty () =
  {fname = name; fty = ty; fbits = bits; fattrs = attrs}

let eitem ?value ~name () = {einame = name; eivalue = value}

(* Pretty printing. *)

let pp_field ppf {fname; fty; fbits; fattrs} =
  Type.pp_named_with Expr.pp ppf fty ~name:fname;
  Option.iter fbits ~f:(fun b ->
      Format.pp_print_string ppf " : ";
      Expr.pp ppf b);
  if not (List.is_empty fattrs) then
    Format.fprintf ppf " %a" Attr.pp_raws fattrs;
  Format.pp_print_char ppf ';'

let pp_eitem ppf {einame; eivalue} =
  Format.pp_print_string ppf einame;
  Option.iter eivalue ~f:(fun v ->
      Format.pp_print_string ppf " = ";
      Expr.pp ppf v)

let pp ppf td = match td.node with
  | Compound {kind; tag; fields; attrs} ->
    let kw = match kind with
      | `struct_ -> "struct"
      | `union -> "union" in
    let pp_tail ppf () =
      if not (List.is_empty attrs) then
        Format.fprintf ppf " %a" Attr.pp_raws attrs;
      Format.pp_print_char ppf ';' in
    begin match fields with
      (* A forward declaration of an incomplete tag. *)
      | None -> Format.fprintf ppf "%s %s%a" kw tag pp_tail ()
      | Some [] -> Format.fprintf ppf "%s %s {}%a" kw tag pp_tail ()
      | Some fields ->
        Format.fprintf ppf "@[<v 2>%s %s {" kw tag;
        List.iter fields ~f:(fun f ->
            Format.fprintf ppf "@,";
            pp_field ppf f);
        Format.fprintf ppf "@]@,}%a" pp_tail ()
    end
  | Enum {tag; items} ->
    begin match items with
      | [] -> Format.fprintf ppf "enum %s {};" tag
      | _ ->
        Format.fprintf ppf "@[<v 2>enum %s {" tag;
        List.iteri items ~f:(fun i it ->
            if i > 0 then Format.pp_print_char ppf ',';
            Format.fprintf ppf "@,";
            pp_eitem ppf it);
        Format.fprintf ppf ",@]@,};"
    end
  | Typedef {name; ty} ->
    Format.pp_print_string ppf "typedef ";
    Type.pp_named_with Expr.pp ppf ty ~name;
    Format.pp_print_char ppf ';'

let to_string td = Format.asprintf "%a" pp td
