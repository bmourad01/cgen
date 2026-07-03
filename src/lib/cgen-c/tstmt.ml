open Core

type localdecl = {
  name : string;
  ty   : Texpr.ty;
  init : Texpr.init option;
} [@@deriving bin_io, compare, equal, hash, sexp]

type instr =
  | Iassign of {
      lval : Texpr.tlval;
      expr : Texpr.t;
    }
  | Icall   of {
      lval : Texpr.tlval option;
      fn   : Texpr.t;
      args : Texpr.t list;
    }
  | Ibuiltin of {
      lval : Texpr.tlval option;
      name : string;
      args : Texpr.t list;
    }
[@@deriving bin_io, compare, equal, hash, sexp]

type forinit =
  | FIexpr of instr list
  | FIdecl of localdecl
[@@deriving bin_io, compare, equal, hash, sexp]

type blkitem =
  | Bstmt of t
  | Bdecl of localdecl
[@@deriving bin_io, compare, equal, hash, sexp]

and t =
  | Sblock of blkitem list
  | Sif of {
      cond  : Texpr.t;
      then_ : t;
      else_ : t option;
    }
  | Swhile of {
      cond : Texpr.t;
      body : t;
    }
  | Sdowhile of {
      body : t;
      cond : Texpr.t;
    }
  | Sfor of {
      init : forinit option;
      cond : Texpr.t option;
      step : instr list;
      body : t;
    }
  | Sswitch of {
      expr : Texpr.t;
      body : t;
    }
  | Scase of {
      value : Cgen.Bv.t;
      body  : t;
    }
  | Sdefault of t
  | Slabel of {
      name : string;
      body : t;
    }
  | Sgoto of string
  | Sbreak
  | Scontinue
  | Sreturn of Texpr.t option
  | Sinstr of instr list
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors. *)

let localdecl ?init ~name ~ty () = {name; ty; init}

let assign ~lval ~expr = Iassign {lval; expr}
let call ?lval ~fn ~args () = Icall {lval; fn; args}
let builtin ?lval ~name ~args () = Ibuiltin {lval; name; args}

let fi_expr instrs = FIexpr instrs
let fi_decl ld = FIdecl ld

let bstmt s = Bstmt s
let bdecl ld = Bdecl ld

let block items = Sblock items
let if_ ?else_ ~cond ~then_ () = Sif {cond; then_; else_}
let while_ ~cond ~body = Swhile {cond; body}
let dowhile ~body ~cond = Sdowhile {body; cond}
let for_ ?init ?cond ~step ~body () = Sfor {init; cond; step; body}
let switch ~expr ~body = Sswitch {expr; body}
let case ~value ~body = Scase {value; body}
let default body = Sdefault body
let label ~name ~body = Slabel {name; body}
let goto name = Sgoto name
let break = Sbreak
let continue = Scontinue
let return ?value () = Sreturn value
let instr instrs = Sinstr instrs

(* Pretty printing *)

let pp_localdecl ppf {name; ty; init} =
  Type.pp_named_with Texpr.pp ppf ty ~name;
  Option.iter init ~f:(fun i ->
      Format.fprintf ppf " = %a" Texpr.pp_init i)

let pp_args ppf args =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
    Texpr.pp ppf args

let pp_instr ppf = function
  | Iassign {lval; expr} ->
    Format.fprintf ppf "%a = %a" Texpr.pp_lval lval Texpr.pp expr
  | Icall {lval = None; fn; args} ->
    Format.fprintf ppf "%a(%a)" Texpr.pp_postfix fn pp_args args
  | Icall {lval = Some lv; fn; args} ->
    Format.fprintf ppf "%a = %a(%a)"
      Texpr.pp_lval lv Texpr.pp_postfix fn pp_args args
  | Ibuiltin {lval = None; name; args} ->
    Format.fprintf ppf "%s(%a)" name pp_args args
  | Ibuiltin {lval = Some lv; name; args} ->
    Format.fprintf ppf "%a = %s(%a)" Texpr.pp_lval lv name pp_args args

let pp_instr_list_inline ppf instrs =
  Format.pp_print_list
    ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
    pp_instr ppf instrs

let pp_forinit ppf = function
  | FIexpr instrs -> pp_instr_list_inline ppf instrs
  | FIdecl ld -> pp_localdecl ppf ld

let is_block s = match s with
  | Sblock _ -> true
  | _ -> false

let rec pp_stmt ppf s = match s with
  | Sblock items -> pp_block ppf items
  | Sif {cond; then_; else_} -> pp_if ppf cond then_ else_
  | Swhile {cond; body} -> pp_while ppf cond body
  | Sdowhile {body; cond} -> pp_dowhile ppf body cond
  | Sfor {init; cond; step; body} ->
    pp_for ppf ~init ~cond ~step ~body
  | Sswitch {expr; body} -> pp_switch ppf expr body
  | Scase _ | Sdefault _ | Slabel _ -> pp_labeled ppf s
  | Sgoto name -> Format.fprintf ppf "goto %s;" name
  | Sbreak -> Format.pp_print_string ppf "break;"
  | Scontinue -> Format.pp_print_string ppf "continue;"
  | Sreturn None -> Format.pp_print_string ppf "return;"
  | Sreturn (Some e) -> Format.fprintf ppf "return %a;" Texpr.pp e
  | Sinstr [] -> Format.pp_print_char ppf ';'
  | Sinstr [i] -> Format.fprintf ppf "%a;" pp_instr i
  | Sinstr instrs ->
    Format.fprintf ppf "(%a);" pp_instr_list_inline instrs

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
  | Bdecl ld ->
    pp_localdecl ppf ld;
    Format.pp_print_char ppf ';'

and pp_if ppf cond then_ else_ =
  Format.fprintf ppf "@[<v 2>if (%a)" Texpr.pp cond;
  pp_inline_body ppf then_;
  Option.iter else_ ~f:(fun e ->
      pp_else ppf ~prev_is_block:(is_block then_) e);
  Format.fprintf ppf "@]"

and pp_else ppf ~prev_is_block e =
  if prev_is_block then Format.pp_print_char ppf ' '
  else Format.fprintf ppf "@;<0 -2>";
  Format.pp_print_string ppf "else";
  match e with
  | Sif {cond; then_; else_} ->
    Format.fprintf ppf " if (%a)" Texpr.pp cond;
    pp_inline_body ppf then_;
    Option.iter else_ ~f:(fun e' ->
        pp_else ppf ~prev_is_block:(is_block then_) e')
  | _ -> pp_inline_body ppf e

and pp_while ppf cond body =
  Format.fprintf ppf "@[<v 2>while (%a)" Texpr.pp cond;
  pp_inline_body ppf body;
  Format.fprintf ppf "@]"

and pp_dowhile ppf body cond =
  Format.fprintf ppf "@[<v 2>do";
  pp_inline_body ppf body;
  if is_block body then Format.pp_print_char ppf ' '
  else Format.fprintf ppf "@;<0 -2>";
  Format.fprintf ppf "while (%a);@]" Texpr.pp cond

and pp_for ppf ~init ~cond ~step ~body =
  Format.fprintf ppf "@[<v 2>for (";
  Option.iter init ~f:(pp_forinit ppf);
  Format.pp_print_string ppf "; ";
  Option.iter cond ~f:(Texpr.pp ppf);
  Format.pp_print_string ppf "; ";
  pp_instr_list_inline ppf step;
  Format.pp_print_char ppf ')';
  pp_inline_body ppf body;
  Format.fprintf ppf "@]"

and pp_switch ppf expr body =
  Format.fprintf ppf "@[<v 2>switch (%a)" Texpr.pp expr;
  pp_inline_body ppf body;
  Format.fprintf ppf "@]"

and pp_labeled ppf s =
  let rec peel acc = function
    | Scase {value; body} ->
      let lbl =
        Format.asprintf "case %a:"
          Z.pp_print (Cgen.Bv.to_bigint value) in
      peel (lbl :: acc) body
    | Sdefault body -> peel ("default:" :: acc) body
    | Slabel {name; body} -> peel ((name ^ ":") :: acc) body
    | body -> List.rev acc, body in
  let labels, body = peel [] s in
  Format.fprintf ppf "@[<v 2>%s" (String.concat ~sep:" " labels);
  begin match body with
    | Sblock _ -> pp_inline_body ppf body
    | _ ->
      Format.pp_print_char ppf ' ';
      pp_stmt ppf body
  end;
  Format.fprintf ppf "@]"

and pp_inline_body ppf body = match body with
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
