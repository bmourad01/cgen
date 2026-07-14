open Core

module Bv = Cgen_utils.Bv

type bop = [
  | Expr.barith
  | Expr.bbitwise
  | Expr.cmp
] [@@deriving bin_io, compare, equal, hash, sexp]

type uop = [
  | Expr.uarith
  | Expr.ubitwise
  | Expr.ulogical
  | `deref
] [@@deriving bin_io, compare, equal, hash, sexp]

type 'n typed = {
  node : 'n;
  ty   : ty;
}

and ty = t Type.t
and t = node typed
and tlval = lval typed

and node =
  | Econst of Expr.const
  | Evar of string
  (** The value of a local variable or parameter after lvalue-to-rvalue
      conversion. *)
  | Esym of string
  (** The value of a global object, named by its link symbol, after
      lvalue-to-rvalue conversion. Distinct from [Evar] so the lowering
      routes it to the symbol even when a same-named local slot is in scope
      (e.g. a block-scope [extern] re-exposing a shadowed global). *)
  | Efun of string
  (** A function designator; decays to a function pointer when
      used as an rvalue. *)
  | Eenum_const of {
      tag   : string;
      name  : string;
      value : Bv.t;
    }
  (** An enum constant with its [int] value already resolved. *)
  | Eunary of {
      op  : uop;
      arg : t;
    }
  | Ebinary of {
      op  : bop;
      lhs : t;
      rhs : t;
    }
  | Eindex of {
      arr : t;
      idx : t;
    }
  | Emember of {
      obj   : t;
      field : string;
    }
  | Eaddrof of tlval
  | Ecast of {
      dst : ty;
      arg : t;
    }
  | Econd of {
      cond  : t;
      then_ : t;
      else_ : t;
    }
  | Ecompound of {
      ty   : ty;
      init : init;
    }

and lval =
  | Lvar of string
  (** A local variable or parameter, designating its stack slot. *)
  | Lsym of string
  (** A global object, designating its link symbol. Distinct from [Lvar]
      so the lowering routes it to the symbol even when a same-named local
      slot is in scope (see [Esym]). *)
  | Lderef  of t
  | Lmember of {
      lval  : tlval;
      field : string;
    }
  | Lindex  of {
      lval  : tlval;
      index : t;
    }

and init =
  | Isingle of t
  | Iarray  of init list
  | Istruct of (string * init) list
  | Iunion  of {
      name : string;
      init : init;
    }
  | Ioverlay of {
      base : t;     (* a whole-aggregate value *)
      over : init;  (* a partial struct init refining it *)
    }
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors for rvalues. *)

let const c ~ty = {node = Econst c; ty}
let var name ~ty = {node = Evar name; ty}
let sym_ name ~ty = {node = Esym name; ty}
let fun_ name ~ty = {node = Efun name; ty}
let enum_const ~tag ~name ~value ~ty = {node = Eenum_const {tag; name; value}; ty}
let unary ~op ~arg ~ty = {node = Eunary {op; arg}; ty}
let binary ~op ~lhs ~rhs ~ty = {node = Ebinary {op; lhs; rhs}; ty}
let index ~arr ~idx ~ty = {node = Eindex {arr; idx}; ty}
let member ~obj ~field ~ty = {node = Emember {obj; field}; ty}
let addrof lv ~ty = {node = Eaddrof lv; ty}
let cast ~dst ~arg = {node = Ecast {dst; arg}; ty = dst}
let cond ~cond ~then_ ~else_ ~ty = {node = Econd {cond; then_; else_}; ty}
let compound ~ty ~init = {node = Ecompound {ty; init}; ty}

(* Constant convenience builders. *)

let int_ ?suffix value ~ty = const (Cint {value; suffix; base = `dec}) ~ty
let str s ~ty = const (Cstr s) ~ty
let char_ c ~ty = const (Cchar c) ~ty
let float_ f ~ty = const (Cfloat f) ~ty
let double d ~ty = const (Cdouble d) ~ty

(* Smart constructors for lvalues. *)

let lvar name ~ty = {node = Lvar name; ty}
let lsym name ~ty = {node = Lsym name; ty}
let lderef e ~ty = {node = Lderef e; ty}
let lmember ~lval ~field ~ty = {node = Lmember {lval; field}; ty}
let lindex ~lval ~index ~ty = {node = Lindex {lval; index}; ty}

(* Smart constructors for initializers. *)

let isingle e = Isingle e
let iarray inits = Iarray inits
let istruct fields = Istruct fields
let iunion ~name ~init = Iunion {name; init}

(* Operator precedence and associativity (delegates to Expr's tables,
   since Texpr's operator alphabets are subsets of Expr's). *)

let prec_bop op = Expr.prec_bop (op :> Expr.bop)
let assoc_bop op = Expr.assoc_bop (op :> Expr.bop)
let prec_uop op = Expr.prec_uop (op :> Expr.uop)

let prec_node = function
  | Econst _
  | Evar _
  | Esym _
  | Efun _
  | Eenum_const _ -> 0
  | Eunary {op; _} -> prec_uop op
  | Ebinary {op; _} -> prec_bop op
  | Eindex _ | Emember _ -> 1
  | Eaddrof _ -> 2
  | Ecast _ | Ecompound _ -> 2
  | Econd _ -> 13

let prec e = prec_node e.node

(* Operator symbols. *)

let bop_symbol op = Expr.bop_symbol (op :> Expr.bop)
let uop_symbol op = Expr.uop_symbol (op :> Expr.uop)

(* Pretty printing. *)

let rec pp_at ~ctx ppf e =
  if prec e > ctx then begin
    Format.pp_print_char ppf '(';
    pp_node ppf e.node;
    Format.pp_print_char ppf ')'
  end else pp_node ppf e.node

and pp_node ppf = function
  | Econst c -> Expr.pp_const ppf c
  | Evar n | Esym n | Efun n -> Format.pp_print_string ppf n
  | Eenum_const {name; _} -> Format.pp_print_string ppf name
  | Eunary {op; arg} ->
    Format.pp_print_string ppf (uop_symbol op);
    pp_at ~ctx:2 ppf arg
  | Ebinary {op; lhs; rhs} ->
    let p = prec_bop op in
    let lctx, rctx = match assoc_bop op with
      | Aleft -> p, p - 1
      | Aright -> p - 1, p in
    pp_at ~ctx:lctx ppf lhs;
    Format.fprintf ppf " %s " (bop_symbol op);
    pp_at ~ctx:rctx ppf rhs
  | Eindex {arr; idx} ->
    pp_at ~ctx:1 ppf arr;
    Format.pp_print_char ppf '[';
    pp_at ~ctx:15 ppf idx;
    Format.pp_print_char ppf ']'
  | Emember {obj; field} ->
    pp_at ~ctx:1 ppf obj;
    Format.pp_print_char ppf '.';
    Format.pp_print_string ppf field
  | Eaddrof lv ->
    Format.pp_print_char ppf '&';
    pp_lval_at ~ctx:2 ppf lv
  | Ecast {dst; arg} ->
    Format.pp_print_char ppf '(';
    Type.pp_with pp ppf dst;
    Format.pp_print_char ppf ')';
    pp_at ~ctx:2 ppf arg
  | Econd {cond; then_; else_} ->
    pp_at ~ctx:12 ppf cond;
    Format.pp_print_string ppf " ? ";
    pp_at ~ctx:15 ppf then_;
    Format.pp_print_string ppf " : ";
    pp_at ~ctx:13 ppf else_
  | Ecompound {ty; init} ->
    Format.pp_print_char ppf '(';
    Type.pp_with pp ppf ty;
    Format.pp_print_char ppf ')';
    pp_init ppf init

and pp_lval ppf lv = match lv.node with
  | Lvar name | Lsym name -> Format.pp_print_string ppf name
  | Lderef e ->
    Format.pp_print_char ppf '*';
    pp_at ~ctx:2 ppf e
  | Lmember {lval; field} ->
    pp_lval_at ~ctx:1 ppf lval;
    Format.pp_print_char ppf '.';
    Format.pp_print_string ppf field
  | Lindex {lval; index} ->
    pp_lval_at ~ctx:1 ppf lval;
    Format.pp_print_char ppf '[';
    pp_at ~ctx:15 ppf index;
    Format.pp_print_char ppf ']'

and pp_lval_at ~ctx ppf lv =
  let p = match lv.node with
    | Lvar _ | Lsym _ -> 0
    | Lderef _ -> 2
    | Lmember _ | Lindex _ -> 1 in
  if p > ctx then begin
    Format.pp_print_char ppf '(';
    pp_lval ppf lv;
    Format.pp_print_char ppf ')'
  end else pp_lval ppf lv

and pp_init ppf = function
  | Isingle e -> pp_at ~ctx:14 ppf e
  | Iarray inits ->
    Format.pp_print_char ppf '{';
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
      pp_init ppf inits;
    Format.pp_print_char ppf '}'
  | Istruct fields ->
    Format.pp_print_char ppf '{';
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
      (fun ppf (name, init) ->
         Format.fprintf ppf ".%s = %a" name pp_init init)
      ppf fields;
    Format.pp_print_char ppf '}'
  | Iunion {name; init} ->
    Format.fprintf ppf "{.%s = %a}" name pp_init init
  | Ioverlay {base; over} ->
    Format.fprintf ppf "%a with %a" (pp_at ~ctx:14) base pp_init over

and pp ppf e = pp_at ~ctx:15 ppf e

let pp_postfix ppf e = pp_at ~ctx:1 ppf e

let to_string e = Format.asprintf "%a" pp e
