open Core

type barith = [
  | `add
  | `sub
  | `mul
  | `div
  | `mod_
] [@@deriving bin_io, compare, equal, hash, sexp]

type blogical = [
  | `land_
  | `lor_
] [@@deriving bin_io, compare, equal, hash, sexp]

type bbitwise = [
  | `and_
  | `or_
  | `xor
  | `shl
  | `shr
] [@@deriving bin_io, compare, equal, hash, sexp]

type eq = [
  | `eq
  | `ne
] [@@deriving bin_io, compare, equal, hash, sexp]

type rel = [
  | `lt
  | `gt
  | `le
  | `ge
] [@@deriving bin_io, compare, equal, hash, sexp]

type cmp = [
  | eq
  | rel
] [@@deriving bin_io, compare, equal, hash, sexp]

type bassign = [
  | `assign
  | `assign_arith of barith
  | `assign_bitwise of bbitwise
] [@@deriving bin_io, compare, equal, hash, sexp]

type bpure = [
  | barith
  | blogical
  | bbitwise
  | cmp
] [@@deriving bin_io, compare, equal, hash, sexp]

type bop = [
  | bpure
  | bassign
] [@@deriving bin_io, compare, equal, hash, sexp]

type uarith = [
  | `minus
  | `plus
] [@@deriving bin_io, compare, equal, hash, sexp]

type ubitwise = [
  | `not_
] [@@deriving bin_io, compare, equal, hash, sexp]

type ulogical = [
  | `lnot_
] [@@deriving bin_io, compare, equal, hash, sexp]

type umem = [
  | `deref
  | `addr
] [@@deriving bin_io, compare, equal, hash, sexp]

type inc = [
  | `preinc
  | `postinc
] [@@deriving bin_io, compare, equal, hash, sexp]

type dec = [
  | `predec
  | `postdec
] [@@deriving bin_io, compare, equal, hash, sexp]

type uassign = [
  | inc
  | dec
] [@@deriving bin_io, compare, equal, hash, sexp]

type upure = [
  | uarith
  | ubitwise
  | ulogical
  | umem
] [@@deriving bin_io, compare, equal, hash, sexp]

type uop = [
  | upure
  | uassign
] [@@deriving bin_io, compare, equal, hash, sexp]

type const =
  | Cint of {
      value : Cgen.Bv.t;
      suffix : [`u | `l | `ul | `ll | `ull] option;
      base : [`dec | `oct | `hex | `bin];
    }
  | Cstr of string
  | Cchar of char
  | Cfloat of Cgen_utils.Float32.t
  | Cdouble of float
[@@deriving bin_io, compare, equal, hash, sexp]

type 'a t = {
  node : 'a node;
  ann  : 'a;
}

and 'a node =
  | Econst of const
  | Ename of string
  | Eunary of {
      op  : uop;
      arg : 'a t;
    }
  | Ebinary of {
      op  : bop;
      lhs : 'a t;
      rhs : 'a t;
    }
  | Eindex of {
      arr : 'a t;
      idx : 'a t;
    }
  | Emember of {
      obj   : 'a t;
      field : string;
    }
  | Earrow of {
      obj   : 'a t;
      field : string;
    }
  | Ecall of {
      callee : 'a t;
      args   : 'a t list;
    }
  | Ecast of {
      dst : 'a ty;
      arg : 'a t;
    }
  | Esizeof_e of 'a t
  | Esizeof_t of 'a ty
  | Econd of {
      cond  : 'a t;
      then_ : 'a t;
      else_ : 'a t;
    }
  | Ecomma of {
      lhs : 'a t;
      rhs : 'a t;
    }
  | Ecompound of {
      ty   : 'a ty;
      init : 'a init;
    }
  | Ebuiltin of {
      name : string;
      args : 'a builtin_arg list;
    }

and 'a ty = 'a t Type.t

and 'a init =
  | Isingle of 'a t
  | Icompound of ('a designator list * 'a init) list

and 'a designator =
  | Dfield of string
  | Dindex of 'a t

(* An argument to a compiler builtin (e.g. `__builtin_va_arg`). Most
   builtins take only expressions; a few (notably `va_arg`) take a type. *)
and 'a builtin_arg =
  | BAexpr of 'a t
  | BAtype of 'a ty
[@@deriving bin_io, compare, equal, hash, sexp]

(* Smart constructors. *)

let const c ~ann = {node = Econst c; ann}
let name n ~ann = {node = Ename n; ann}
let unary ~op ~arg ~ann = {node = Eunary {op; arg}; ann}
let binary ~op ~lhs ~rhs ~ann = {node = Ebinary {op; lhs; rhs}; ann}
let index ~arr ~idx ~ann = {node = Eindex {arr; idx}; ann}
let member ~obj ~field ~ann = {node = Emember {obj; field}; ann}
let arrow ~obj ~field ~ann = {node = Earrow {obj; field}; ann}
let call ~callee ~args ~ann = {node = Ecall {callee; args}; ann}
let cast ~dst ~arg ~ann = {node = Ecast {dst; arg}; ann}
let sizeof_e e ~ann = {node = Esizeof_e e; ann}
let sizeof_t ty ~ann = {node = Esizeof_t ty; ann}
let cond ~cond ~then_ ~else_ ~ann = {node = Econd {cond; then_; else_}; ann}
let comma ~lhs ~rhs ~ann = {node = Ecomma {lhs; rhs}; ann}
let compound ~ty ~init ~ann = {node = Ecompound {ty; init}; ann}
let builtin ~name ~args ~ann = {node = Ebuiltin {name; args}; ann}

(* Constant convenience builders. *)

let int_ ?suffix ?(base = `dec) value ~ann = const (Cint {value; suffix; base}) ~ann
let str s ~ann = const (Cstr s) ~ann
let char_ c ~ann = const (Cchar c) ~ann
let float_ f ~ann = const (Cfloat f) ~ann
let double d ~ann = const (Cdouble d) ~ann

(* Operator precedence and associativity. *)

type assoc = Aleft | Aright

let prec_bop : bop -> int = function
  | `mul | `div | `mod_ -> 3
  | `add | `sub -> 4
  | `shl | `shr -> 5
  | `lt | `gt | `le | `ge -> 6
  | `eq | `ne -> 7
  | `and_ -> 8
  | `xor -> 9
  | `or_ -> 10
  | `land_ -> 11
  | `lor_ -> 12
  | `assign
  | `assign_arith _
  | `assign_bitwise _ -> 14

let assoc_bop : bop -> assoc = function
  | `assign
  | `assign_arith _
  | `assign_bitwise _ -> Aright
  | _ -> Aleft

let prec_uop : uop -> int = function
  | `postinc | `postdec -> 1
  | _ -> 2

let uop_is_postfix : uop -> bool = function
  | `postinc | `postdec -> true
  | _ -> false

let prec_node : type a. a node -> int = function
  | Econst _ | Ename _ -> 0
  | Eunary {op; _} -> prec_uop op
  | Ebinary {op; _} -> prec_bop op
  | Eindex _
  | Emember _
  | Earrow _
  | Ecall _ -> 1
  | Ecast _
  | Esizeof_e _
  | Esizeof_t _
  | Ecompound _ -> 2
  | Ebuiltin _ -> 1
  | Econd _ -> 13
  | Ecomma _ -> 15

let prec e = prec_node e.node

(* Operator symbols. *)

let bop_symbol : bop -> string = function
  | `add -> "+"
  | `sub -> "-"
  | `mul -> "*"
  | `div -> "/"
  | `mod_ -> "%"
  | `land_ -> "&&"
  | `lor_ -> "||"
  | `and_ -> "&"
  | `or_ -> "|"
  | `xor -> "^"
  | `shl -> "<<"
  | `shr -> ">>"
  | `eq -> "=="
  | `ne -> "!="
  | `lt -> "<"
  | `gt -> ">"
  | `le -> "<="
  | `ge -> ">="
  | `assign -> "="
  | `assign_arith `add -> "+="
  | `assign_arith `sub -> "-="
  | `assign_arith `mul -> "*="
  | `assign_arith `div -> "/="
  | `assign_arith `mod_ -> "%="
  | `assign_bitwise `and_ -> "&="
  | `assign_bitwise `or_ -> "|="
  | `assign_bitwise `xor -> "^="
  | `assign_bitwise `shl -> "<<="
  | `assign_bitwise `shr -> ">>="

let uop_symbol : uop -> string = function
  | `minus   -> "-"
  | `plus    -> "+"
  | `not_    -> "~"
  | `lnot_   -> "!"
  | `deref   -> "*"
  | `addr    -> "&"
  | `preinc  -> "++"
  | `postinc -> "++"
  | `predec  -> "--"
  | `postdec -> "--"

(* Pretty printing. *)

(* C character escapes for use inside literals. *)
let pp_escaped_char ppf ~in_string = function
  | '\n' -> Format.pp_print_string ppf "\\n"
  | '\t' -> Format.pp_print_string ppf "\\t"
  | '\r' -> Format.pp_print_string ppf "\\r"
  | '\\' -> Format.pp_print_string ppf "\\\\"
  | '"'  when in_string -> Format.pp_print_string ppf "\\\""
  | '\'' when not in_string -> Format.pp_print_string ppf "\\'"
  | c when Char.is_print c -> Format.pp_print_char ppf c
  | c -> Format.fprintf ppf "\\x%02x" (Char.to_int c)

let pp_int_suffix ppf = function
  | None      -> ()
  | Some `u   -> Format.pp_print_char ppf 'u'
  | Some `l   -> Format.pp_print_char ppf 'l'
  | Some `ul  -> Format.pp_print_string ppf "ul"
  | Some `ll  -> Format.pp_print_string ppf "ll"
  | Some `ull -> Format.pp_print_string ppf "ull"

let pp_const ppf = function
  | Cint {value; suffix; _} ->
    Z.pp_print ppf (Cgen.Bv.to_bigint value);
    pp_int_suffix ppf suffix
  | Cstr s ->
    Format.pp_print_char ppf '"';
    String.iter s ~f:(pp_escaped_char ppf ~in_string:true);
    Format.pp_print_char ppf '"'
  | Cchar c ->
    Format.pp_print_char ppf '\'';
    pp_escaped_char ppf ~in_string:false c;
    Format.pp_print_char ppf '\''
  | Cfloat f ->
    Format.fprintf ppf "%h" (Cgen_utils.Float32.to_float f);
    Format.pp_print_char ppf 'f'
  | Cdouble d ->
    Format.fprintf ppf "%h" d

let rec pp_at ~ctx ppf e =
  if prec e > ctx then begin
    Format.pp_print_char ppf '(';
    pp_node ppf e.node;
    Format.pp_print_char ppf ')'
  end else pp_node ppf e.node

and pp_node ppf = function
  | Econst c -> pp_const ppf c
  | Ename n -> Format.pp_print_string ppf n
  | Eunary {op; arg} ->
    if uop_is_postfix op then begin
      pp_at ~ctx:1 ppf arg;
      Format.pp_print_string ppf (uop_symbol op)
    end else begin
      Format.pp_print_string ppf (uop_symbol op);
      pp_at ~ctx:2 ppf arg
    end
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
  | Earrow {obj; field} ->
    pp_at ~ctx:1 ppf obj;
    Format.pp_print_string ppf "->";
    Format.pp_print_string ppf field
  | Ecall {callee; args} ->
    pp_at ~ctx:1 ppf callee;
    Format.pp_print_char ppf '(';
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
      (fun ppf e -> pp_at ~ctx:14 ppf e) ppf args;
    Format.pp_print_char ppf ')'
  | Ecast {dst; arg} ->
    Format.pp_print_char ppf '(';
    Type.pp_with pp ppf dst;
    Format.pp_print_char ppf ')';
    pp_at ~ctx:2 ppf arg
  | Esizeof_e arg ->
    Format.pp_print_string ppf "sizeof ";
    pp_at ~ctx:2 ppf arg
  | Esizeof_t ty ->
    Format.pp_print_string ppf "sizeof(";
    Type.pp_with pp ppf ty;
    Format.pp_print_char ppf ')'
  | Econd {cond; then_; else_} ->
    pp_at ~ctx:12 ppf cond;
    Format.pp_print_string ppf " ? ";
    pp_at ~ctx:15 ppf then_;
    Format.pp_print_string ppf " : ";
    pp_at ~ctx:13 ppf else_
  | Ecomma {lhs; rhs} ->
    pp_at ~ctx:15 ppf lhs;
    Format.pp_print_string ppf ", ";
    pp_at ~ctx:14 ppf rhs
  | Ecompound {ty; init} ->
    Format.pp_print_char ppf '(';
    Type.pp_with pp ppf ty;
    Format.pp_print_char ppf ')';
    pp_init ppf init
  | Ebuiltin {name; args} ->
    Format.pp_print_string ppf name;
    Format.pp_print_char ppf '(';
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
      pp_builtin_arg ppf args;
    Format.pp_print_char ppf ')'

and pp_builtin_arg ppf = function
  | BAexpr e -> pp_at ~ctx:14 ppf e
  | BAtype ty -> Type.pp_with pp ppf ty

and pp_init ppf = function
  | Isingle e -> pp_at ~ctx:14 ppf e
  | Icompound items ->
    Format.pp_print_char ppf '{';
    Format.pp_print_list
      ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
      (fun ppf -> function
         | [], sub -> pp_init ppf sub
         | ds, sub ->
           List.iter ds ~f:(pp_designator ppf);
           Format.pp_print_string ppf " = ";
           pp_init ppf sub)
      ppf items;
    Format.pp_print_char ppf '}'

and pp_designator ppf = function
  | Dfield s ->
    Format.pp_print_char ppf '.';
    Format.pp_print_string ppf s
  | Dindex e ->
    Format.pp_print_char ppf '[';
    pp_at ~ctx:15 ppf e;
    Format.pp_print_char ppf ']'

and pp ppf e = pp_at ~ctx:15 ppf e

let to_string e = Format.asprintf "%a" pp e
