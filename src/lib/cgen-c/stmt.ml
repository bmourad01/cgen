open Core

type storagecls =
  | SCdefault
  | SCauto
  | SCstatic
  | SCregister
  | SCextern
[@@deriving bin_io, compare, equal, hash, sexp]

type 'a localdecl = {
  ldname    : string;
  ldty      : 'a Expr.ty;
  ldinit    : 'a Expr.init option;
  ldstorage : storagecls;
  ldattrs   : 'a Attr.raws;
  ldann     : 'a;
} [@@deriving bin_io, compare, equal, hash, sexp]

type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Sblock of 'a blkitem list
  | Sif of {
      cond  : 'a Expr.t;
      then_ : 'a t;
      else_ : 'a t option;
    }
  | Swhile of {
      cond : 'a Expr.t;
      body : 'a t;
    }
  | Sdowhile of {
      body : 'a t;
      cond : 'a Expr.t;
    }
  | Sfor of {
      init : 'a forinit option;
      cond : 'a Expr.t option;
      step : 'a Expr.t option;
      body : 'a t;
    }
  | Sswitch of {
      expr : 'a Expr.t;
      body : 'a t;
    }
  | Scase of {
      value : 'a Expr.t;
      body  : 'a t;
    }
  | Sdefault of 'a t
  | Slabel of {
      name : string;
      body : 'a t;
    }
  | Sgoto of string
  | Sgotoind of 'a Expr.t
  | Sbreak
  | Scontinue
  | Sreturn of 'a Expr.t option
  | Sexpr of 'a Expr.t
  | Snull

and 'a forinit =
  | FIexpr of 'a Expr.t
  | FIdecl of 'a localdecl list

and 'a blkitem =
  | Bstmt of 'a t
  | Bdecl of 'a localdecl list
  | Btype of 'a Tydecl.t list
  (** Block-scope struct/union/enum/typedef definitions (see {!Tydecl}). *)
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors. *)

let block items ~ann = {node = Sblock items; ann}
let if_ ?else_ ~cond ~then_ ~ann () = {node = Sif {cond; then_; else_}; ann}
let while_ ~cond ~body ~ann = {node = Swhile {cond; body}; ann}
let dowhile ~body ~cond ~ann = {node = Sdowhile {body; cond}; ann}
let for_ ?init ?cond ?step ~body ~ann () = {node = Sfor {init; cond; step; body}; ann}
let switch ~expr ~body ~ann = {node = Sswitch {expr; body}; ann}
let case ~value ~body ~ann = {node = Scase {value; body}; ann}
let default body ~ann = {node = Sdefault body; ann}
let label ~name ~body ~ann = {node = Slabel {name; body}; ann}
let goto name ~ann = {node = Sgoto name; ann}
let gotoind e ~ann = {node = Sgotoind e; ann}
let break ~ann = {node = Sbreak; ann}
let continue ~ann = {node = Scontinue; ann}
let return ?value ~ann () = {node = Sreturn value; ann}
let expr e ~ann = {node = Sexpr e; ann}
let null ~ann = {node = Snull; ann}

let localdecl ?init ?(storage = SCdefault) ?(attrs = []) ~name ~ty ~ann () = {
  ldname = name;
  ldty = ty;
  ldinit = init;
  ldstorage = storage;
  ldattrs = attrs;
  ldann = ann;
}

(* Pretty printing. *)

let pp_storagecls ppf = function
  | SCdefault  -> ()
  | SCauto     -> Format.pp_print_string ppf "auto "
  | SCstatic   -> Format.pp_print_string ppf "static "
  | SCregister -> Format.pp_print_string ppf "register "
  | SCextern   -> Format.pp_print_string ppf "extern "

(* Render a single localdecl in full:

   1. storage class
   2. type
   3. name
   4. optional initializer

   No trailing semicolon.
*)
let pp_localdecl ppf {ldname; ldty; ldinit; ldstorage; ldattrs; ldann = _} =
  pp_storagecls ppf ldstorage;
  Type.pp_named_with Expr.pp ppf ldty ~name:ldname;
  if not (List.is_empty ldattrs) then
    Format.fprintf ppf " %a" Attr.pp_raws ldattrs;
  Option.iter ldinit ~f:(fun i ->
      Format.pp_print_string ppf " = ";
      Expr.pp_init ppf i)

(* Render an init-declarator continuation (no specifier).

   Used after a preceding pp_localdecl when emitting
   a comma-separated list that shares a single specifier.
*)
let pp_localdecl_cont ppf {ldname; ldty; ldinit; _} =
  Type.pp_declarator_with Expr.pp ppf ldty ~name:ldname;
  Option.iter ldinit ~f:(fun i ->
      Format.pp_print_string ppf " = ";
      Expr.pp_init ppf i)

(* Render a list of localdecls as a single C declaration, e.g.:

   ```c
   int x, *y = NULL, z[3];
   ```

   The shared specifier is taken from the first decl.
*)
let pp_localdecl_list ppf = function
  | [] -> ()
  | first :: rest ->
    pp_localdecl ppf first;
    List.iter rest ~f:(fun d ->
        Format.pp_print_string ppf ", ";
        pp_localdecl_cont ppf d)

let pp_forinit ppf = function
  | FIexpr e  -> Expr.pp ppf e
  | FIdecl ds -> pp_localdecl_list ppf ds

let is_block s = match s.node with
  | Sblock _ -> true
  | _ -> false

let rec pp_stmt ppf s = match s.node with
  | Sblock items -> pp_block ppf items
  | Sif {cond; then_; else_} -> pp_if ppf cond then_ else_
  | Swhile {cond; body} -> pp_while ppf cond body
  | Sdowhile {body; cond} -> pp_dowhile ppf body cond
  | Sfor {init; cond; step; body} -> pp_for ppf ~init ~cond ~step ~body
  | Sswitch {expr; body} -> pp_switch ppf expr body
  | Scase {value; body} ->
    Format.fprintf ppf "case %a: %a" Expr.pp value pp_stmt body
  | Sdefault body ->
    Format.fprintf ppf "default: %a" pp_stmt body
  | Slabel {name; body} ->
    Format.fprintf ppf "%s: %a" name pp_stmt body
  | Sgoto name -> Format.fprintf ppf "goto %s;" name
  | Sgotoind e -> Format.fprintf ppf "goto *%a;" Expr.pp e
  | Sbreak -> Format.pp_print_string ppf "break;"
  | Scontinue -> Format.pp_print_string ppf "continue;"
  | Sreturn None -> Format.pp_print_string ppf "return;"
  | Sreturn (Some e) -> Format.fprintf ppf "return %a;" Expr.pp e
  | Sexpr e -> Format.fprintf ppf "%a;" Expr.pp e
  | Snull -> Format.pp_print_char ppf ';'

and pp_block ppf = function
  | [] -> Format.pp_print_string ppf "{}"
  | items ->
    Format.fprintf ppf "@[<v 2>{";
    List.iter items ~f:(fun item ->
        Format.fprintf ppf "@,";
        pp_blkitem ppf item);
    Format.fprintf ppf "@]@,}"

and pp_blkitem ppf = function
  | Bstmt s -> pp_stmt ppf s
  | Bdecl ds ->
    pp_localdecl_list ppf ds;
    Format.pp_print_char ppf ';'
  | Btype tds ->
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.pp_print_cut ppf ())
      Tydecl.pp ppf tds

and pp_if ppf cond then_ else_ =
  Format.fprintf ppf "@[<v 2>if (%a)" Expr.pp cond;
  pp_inline_body ppf then_;
  Option.iter else_ ~f:(fun e ->
      pp_else ppf ~prev_is_block:(is_block then_) e);
  Format.fprintf ppf "@]"

and pp_else ppf ~prev_is_block e =
  if prev_is_block then Format.pp_print_char ppf ' '
  else Format.fprintf ppf "@;<0 -2>";
  Format.pp_print_string ppf "else";
  match e.node with
  | Sif {cond; then_; else_} ->
    (* `else if` chain: inline the nested `if` into this vbox so
       all branches share the same indent. *)
    Format.fprintf ppf " if (%a)" Expr.pp cond;
    pp_inline_body ppf then_;
    Option.iter else_ ~f:(fun e' ->
        pp_else ppf ~prev_is_block:(is_block then_) e')
  | _ -> pp_inline_body ppf e

and pp_while ppf cond body =
  Format.fprintf ppf "@[<v 2>while (%a)" Expr.pp cond;
  pp_inline_body ppf body;
  Format.fprintf ppf "@]"

and pp_dowhile ppf body cond =
  Format.fprintf ppf "@[<v 2>do";
  pp_inline_body ppf body;
  if is_block body then Format.pp_print_char ppf ' '
  else Format.fprintf ppf "@;<0 -2>";
  Format.fprintf ppf "while (%a);@]" Expr.pp cond

and pp_for ppf ~init ~cond ~step ~body =
  Format.fprintf ppf "@[<v 2>for (";
  Option.iter init ~f:(pp_forinit ppf);
  Format.pp_print_string ppf "; ";
  Option.iter cond ~f:(Expr.pp ppf);
  Format.pp_print_string ppf "; ";
  Option.iter step ~f:(Expr.pp ppf);
  Format.pp_print_char ppf ')';
  pp_inline_body ppf body;
  Format.fprintf ppf "@]"

and pp_switch ppf expr body =
  Format.fprintf ppf "@[<v 2>switch (%a)" Expr.pp expr;
  pp_inline_body ppf body;
  Format.fprintf ppf "@]"

and pp_inline_body ppf body = match body.node with
  | Sblock [] -> Format.pp_print_string ppf " {}"
  | Sblock items ->
    Format.pp_print_string ppf " {";
    List.iter items ~f:(fun item ->
        Format.fprintf ppf "@,";
        pp_blkitem ppf item);
    Format.fprintf ppf "@;<0 -2>}"
  | _ ->
    Format.fprintf ppf "@,";
    pp_stmt ppf body

let pp = pp_stmt
let to_string s = Format.asprintf "%a" pp s
