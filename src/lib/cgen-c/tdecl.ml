open Core

type linkage =
  | Lextern
  | Lstatic
[@@deriving bin_io, compare, equal, hash, sexp]

type param = {
  pname : string;
  pty   : Texpr.ty;
} [@@deriving bin_io, compare, equal, hash, sexp]

type field = {
  fname : string;
  fty   : Texpr.ty;
  fbits : int option;
} [@@deriving bin_io, compare, equal, hash, sexp]

type t =
  | Dfundef of {
      name     : string;
      params   : param list;
      variadic : bool;
      ret      : Texpr.ty;
      body     : Tstmt.t;
      linkage  : linkage;
      inline   : bool;
      noreturn : bool;
    }
  | Dfundecl of {
      name     : string;
      params   : param list;
      variadic : bool;
      ret      : Texpr.ty;
      linkage  : linkage;
    }
  | Dglobal of {
      name    : string;
      ty      : Texpr.ty;
      init    : Texpr.init option;
      linkage : linkage;
      tls     : bool;
    }
  | Dextern of {
      name    : string;
      ty      : Texpr.ty;
      linkage : linkage;
      tls     : bool;
    }
  | Dcompound of {
      kind   : Type.compound;
      tag    : string;
      fields : field list;
    }
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors. *)

let param ~name ~ty = {pname = name; pty = ty}
let field ?bits ~name ~ty () = {fname = name; fty = ty; fbits = bits}

let fundef
    ?(variadic = false)
    ?(linkage = Lextern)
    ?(inline = false)
    ?(noreturn = false)
    ~name ~params ~ret ~body () =
  Dfundef {name; params; variadic; ret; body; linkage; inline; noreturn}

let fundecl
    ?(variadic = false)
    ?(linkage = Lextern)
    ~name ~params ~ret () =
  Dfundecl {name; params; variadic; ret; linkage}

let global
    ?init
    ?(linkage = Lextern)
    ?(tls = false)
    ~name ~ty () =
  Dglobal {name; ty; init; linkage; tls}

let extern
    ?(linkage = Lextern)
    ?(tls = false)
    ~name ~ty () =
  Dextern {name; ty; linkage; tls}

let compound ~kind ~tag ~fields = Dcompound {kind; tag; fields}

(* Pretty printing. *)

let to_type_params (ps : param list) : Texpr.t Type.param list =
  List.map ps ~f:(fun {pname; pty} ->
      {Type.pname = Some pname; ptype = pty})

let pp_param ppf {pname; pty} =
  Type.pp_named_with Texpr.pp ppf pty ~name:pname

let pp_field ppf {fname; fty; fbits} =
  Type.pp_named_with Texpr.pp ppf fty ~name:fname;
  Option.iter fbits ~f:(fun b -> Format.fprintf ppf " : %d" b);
  Format.pp_print_char ppf ';'

let pp_linkage_prefix ppf = function
  | Lextern -> ()
  | Lstatic -> Format.pp_print_string ppf "static "

let pp_tls ppf tls =
  if tls then Format.pp_print_string ppf "_Thread_local "

let pp_function_modifiers ppf ~inline ~noreturn =
  if inline   then Format.pp_print_string ppf "inline ";
  if noreturn then Format.pp_print_string ppf "_Noreturn "

let pp ppf = function
  | Dfundef {name; params; variadic; ret; body; linkage; inline; noreturn} ->
    Format.fprintf ppf "@[<v 2>";
    pp_linkage_prefix ppf linkage;
    pp_function_modifiers ppf ~inline ~noreturn;
    let ty =
      Type.fun_
        ~result:ret
        ~params:(to_type_params params)
        ~variadic () in
    Type.pp_named_with Texpr.pp ppf ty ~name;
    Tstmt.pp_inline_body ppf body;
    Format.fprintf ppf "@]"
  | Dfundecl {name; params; variadic; ret; linkage} ->
    pp_linkage_prefix ppf linkage;
    let ty =
      Type.fun_
        ~result:ret
        ~params:(to_type_params params)
        ~variadic () in
    Type.pp_named_with Texpr.pp ppf ty ~name;
    Format.pp_print_char ppf ';'
  | Dglobal {name; ty; init; linkage; tls} ->
    pp_linkage_prefix ppf linkage;
    pp_tls ppf tls;
    Type.pp_named_with Texpr.pp ppf ty ~name;
    Option.iter init ~f:(fun i ->
        Format.fprintf ppf " = %a" Texpr.pp_init i);
    Format.pp_print_char ppf ';'
  | Dextern {name; ty; linkage = _; tls} ->
    Format.pp_print_string ppf "extern ";
    pp_tls ppf tls;
    Type.pp_named_with Texpr.pp ppf ty ~name;
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

let to_string d = Format.asprintf "%a" pp d
