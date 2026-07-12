open Core

type 'a param = {
  pname : string option;
  pty   : 'a Expr.ty;
} [@@deriving bin_io, compare, equal, hash, sexp]

type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Dfun of {
      name     : string;
      params   : 'a param list;
      variadic : bool;
      ret      : 'a Expr.ty;
      body     : 'a Stmt.t option;
      storage  : Stmt.storagecls;
      inline   : bool;
      attrs    : 'a Attr.raws;
    }
  | Dvar of {
      name    : string;
      ty      : 'a Expr.ty;
      init    : 'a Expr.init option;
      storage : Stmt.storagecls;
      tls     : bool;
      attrs   : 'a Attr.raws;
    }
  | Dtype of 'a Tydecl.t
  (** A struct/union/enum/typedef definition (see {!Tydecl}). *)
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors. *)

let fun_
    ?(variadic = false)
    ?body
    ?(storage = Stmt.SCdefault)
    ?(inline = false)
    ?(attrs = [])
    ~name ~params ~ret ~ann () =
  {node = Dfun {name; params; variadic; ret; body; storage; inline; attrs}; ann}

let var
    ?init
    ?(storage = Stmt.SCdefault)
    ?(tls = false)
    ?(attrs = [])
    ~name ~ty ~ann () =
  {node = Dvar {name; ty; init; storage; tls; attrs}; ann}

(* Wrap a type declaration (see {!Tydecl}) as a declaration. *)
let of_tydecl (td : 'a Tydecl.t) = {node = Dtype td; ann = td.ann}

let param ?name ~ty () = {pname = name; pty = ty}

(* Pretty printing. *)

(* Convert [Decl] params to [Type] params, so that the function-type
   printer can produce a proper declarator (with the spiral-rule parens). *)
let to_type_params (ps : 'a param list) : 'a Expr.t Type.param list =
  List.map ps ~f:(fun {pname; pty} -> {Type.pname; ptype = pty})

let pp_param ppf {pname; pty} =
  let name = Option.value pname ~default:"" in
  Type.pp_named_with Expr.pp ppf pty ~name

let pp_tls ppf tls =
  if tls then Format.pp_print_string ppf "_Thread_local "

(* Attributes render as written, including [_Noreturn], which parses to a
   `noreturn` attribute. *)
let pp_attrs ppf attrs = match attrs with
  | [] -> ()
  | _ -> Format.fprintf ppf "%a " Attr.pp_raws attrs

let pp_function_modifiers ppf ~inline ~attrs =
  if inline then Format.pp_print_string ppf "inline ";
  pp_attrs ppf attrs

let pp ppf decl = match decl.node with
  | Dfun {name; params; variadic; ret; body; storage; inline; attrs} ->
    Format.fprintf ppf "@[<v 2>";
    Stmt.pp_storagecls ppf storage;
    pp_function_modifiers ppf ~inline ~attrs;
    let ty =
      Type.fun_
        ~result:ret
        ~params:(to_type_params params)
        ~variadic () in
    Type.pp_named_with Expr.pp ppf ty ~name;
    begin match body with
      | None -> Format.pp_print_char ppf ';'
      | Some s -> Stmt.pp_inline_body ppf s
    end;
    Format.fprintf ppf "@]"
  | Dvar {name; ty; init; storage; tls; attrs} ->
    Stmt.pp_storagecls ppf storage;
    pp_tls ppf tls;
    pp_attrs ppf attrs;
    Type.pp_named_with Expr.pp ppf ty ~name;
    Option.iter init ~f:(fun i ->
        Format.pp_print_string ppf " = ";
        Expr.pp_init ppf i);
    Format.pp_print_char ppf ';'
  | Dtype td -> Tydecl.pp ppf td

let to_string d = Format.asprintf "%a" pp d
