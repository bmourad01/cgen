open Core

type 'a param = {
  pname : string option;
  pty   : 'a Expr.ty;
} [@@deriving bin_io, compare, equal, hash, sexp]

type 'a field = {
  fname : string;
  fty   : 'a Expr.ty;
  fbits : 'a Expr.t option;
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
  | Dfun of {
      name     : string;
      params   : 'a param list;
      variadic : bool;
      ret      : 'a Expr.ty;
      body     : 'a Stmt.t option;
      storage  : Stmt.storagecls;
      inline   : bool;
      noreturn : bool;
    }
  | Dvar of {
      name    : string;
      ty      : 'a Expr.ty;
      init    : 'a Expr.init option;
      storage : Stmt.storagecls;
      tls     : bool;
    }
  | Dcompound of {
      kind   : Type.compound;
      tag    : string;
      fields : 'a field list;
    }
  | Denum of {
      tag   : string;
      items : 'a eitem list;
    }
  | Dtypedef of {
      name : string;
      ty   : 'a Expr.ty;
    }
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors. *)

let fun_
    ?(variadic = false)
    ?body
    ?(storage = Stmt.SCdefault)
    ?(inline = false)
    ?(noreturn = false)
    ~name ~params ~ret ~ann () =
  {node = Dfun {name; params; variadic; ret; body; storage; inline; noreturn}; ann}

let var
    ?init
    ?(storage = Stmt.SCdefault)
    ?(tls = false)
    ~name ~ty ~ann () =
  {node = Dvar {name; ty; init; storage; tls}; ann}

let compound ~kind ~tag ~fields ~ann =
  {node = Dcompound {kind; tag; fields}; ann}

let enum ~tag ~items ~ann =
  {node = Denum {tag; items}; ann}

let typedef ~name ~ty ~ann =
  {node = Dtypedef {name; ty}; ann}

let param ?name ~ty () = {pname = name; pty = ty}
let field ?bits ~name ~ty () = {fname = name; fty = ty; fbits = bits}
let eitem ?value ~name () = {einame = name; eivalue = value}

(* Pretty printing. *)

(* Convert [Decl] params to [Type] params, so that the function-type
   printer can produce a proper declarator (with the spiral-rule parens). *)
let to_type_params (ps : 'a param list) : 'a Expr.t Type.param list =
  List.map ps ~f:(fun {pname; pty} -> {Type.pname; ptype = pty})

let pp_param ppf {pname; pty} =
  let name = Option.value pname ~default:"" in
  Type.pp_named_with Expr.pp ppf pty ~name

let pp_field ppf {fname; fty; fbits} =
  Type.pp_named_with Expr.pp ppf fty ~name:fname;
  Option.iter fbits ~f:(fun b ->
      Format.pp_print_string ppf " : ";
      Expr.pp ppf b);
  Format.pp_print_char ppf ';'

let pp_eitem ppf {einame; eivalue} =
  Format.pp_print_string ppf einame;
  Option.iter eivalue ~f:(fun v ->
      Format.pp_print_string ppf " = ";
      Expr.pp ppf v)

let pp_tls ppf tls =
  if tls then Format.pp_print_string ppf "_Thread_local "

let pp_function_modifiers ppf ~inline ~noreturn =
  if inline   then Format.pp_print_string ppf "inline ";
  if noreturn then Format.pp_print_string ppf "_Noreturn "

let pp ppf decl = match decl.node with
  | Dfun {name; params; variadic; ret; body; storage; inline; noreturn} ->
    Format.fprintf ppf "@[<v 2>";
    Stmt.pp_storagecls ppf storage;
    pp_function_modifiers ppf ~inline ~noreturn;
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
  | Dvar {name; ty; init; storage; tls} ->
    Stmt.pp_storagecls ppf storage;
    pp_tls ppf tls;
    Type.pp_named_with Expr.pp ppf ty ~name;
    Option.iter init ~f:(fun i ->
        Format.pp_print_string ppf " = ";
        Expr.pp_init ppf i);
    Format.pp_print_char ppf ';'
  | Dcompound {kind; tag; fields} ->
    let kw = match kind with `struct_ -> "struct" | `union -> "union" in
    begin match fields with
      | [] -> Format.fprintf ppf "%s %s {};" kw tag
      | _ ->
        Format.fprintf ppf "@[<v 2>%s %s {" kw tag;
        List.iter fields ~f:(fun f ->
            Format.fprintf ppf "@,";
            pp_field ppf f);
        Format.fprintf ppf "@]@,};"
    end
  | Denum {tag; items} ->
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
  | Dtypedef {name; ty} ->
    Format.pp_print_string ppf "typedef ";
    Type.pp_named_with Expr.pp ppf ty ~name;
    Format.pp_print_char ppf ';'

let to_string d = Format.asprintf "%a" pp d
