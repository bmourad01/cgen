open Core
open Virtual.Abi

module Id = Int

type id = Id.t [@@deriving compare, equal, hash, sexp]

module Pattern = struct
  type op =
    | Oaddr   of Bv.t
    | Obinop  of Insn.binop
    | Obool   of bool
    | Obr
    | Ocall
    | Odouble of float
    | Ohlt
    | Ojmp
    | Oint    of Bv.t * Type.imm
    | Oload   of Type.basic
    | Olocal  of Label.t
    | Omove
    | Oret
    | Osel    of Type.basic
    | Osingle of Float32.t
    | Ostore  of [Type.basic | `v128]
    | Osw     of Type.imm
    | Osym    of string * int
    | Ounop   of Insn.unop
  [@@deriving compare, equal, hash, sexp]

  type exp = Exp
  type stmt = Stmt

  type ('a, 'b) t =
    | V : string -> ('a, 'b) t
    | P : op * ('b, 'c) t list -> ('a, 'b) t

  type toplevel = (stmt, exp) t
  type sub = (exp, exp) t

  let pp_op ppf = function
    | Oaddr a -> Format.fprintf ppf "addr:%a" Bv.pp a
    | Obinop b -> Format.fprintf ppf "%a" Insn.pp_binop b
    | Obool b -> Format.fprintf ppf "%b" b
    | Obr -> Format.fprintf ppf "br"
    | Ocall -> Format.fprintf ppf "call"
    | Odouble d -> Format.fprintf ppf "%a_d" Float.pp d
    | Ohlt -> Format.fprintf ppf "hlt"
    | Ojmp -> Format.fprintf ppf "jmp"
    | Oint (i, t) -> Format.fprintf ppf "%a_%a" Bv.pp i Type.pp_imm t
    | Oload t -> Format.fprintf ppf "ld.%a" Type.pp_basic t
    | Olocal l -> Format.fprintf ppf "%a" Label.pp l
    | Omove -> Format.fprintf ppf "move"
    | Oret -> Format.fprintf ppf "ret"
    | Osel t -> Format.fprintf ppf "sel.%a" Type.pp_basic t
    | Osingle s -> Format.fprintf ppf "%s_s" (Float32.to_string s)
    | Ostore `v128 -> Format.fprintf ppf "st.v"
    | Ostore (#Type.basic as t) -> Format.fprintf ppf "st.%a" Type.pp_basic t
    | Osw t -> Format.fprintf ppf "sw.%a" Type.pp_imm t
    | Osym (s, o) -> Format.fprintf ppf "$%s+%d" s o
    | Ounop u -> Format.fprintf ppf "%a" Insn.pp_unop u

  let rec pp : type a b. Format.formatter -> (a, b) t -> unit =
    fun ppf -> function
      | V x -> Format.fprintf ppf "?%s" x
      | P (o, []) -> Format.fprintf ppf "%a" pp_op o
      | P (o, ps) ->
        let pp_sep ppf () = Format.fprintf ppf " " in
        Format.fprintf ppf "(%a %a)"
          pp_op o
          (Format.pp_print_list ~pp_sep pp)
          ps
end

module Subst = struct
  type 'r term =
    | Regvar of 'r * Type.basic
    | Regvar_v of 'r
    | Imm of Bv.t * Type.imm
    | Single of Float32.t
    | Double of float
    | Sym of string * int
    | Label of Label.t
    | Bool of bool
    | Table of Label.t * (Bv.t * Label.t) list
    | Callargs of 'r list
  [@@deriving equal, sexp]

  type 'r info = {
    id : id;
    tm : 'r term;
  } [@@deriving sexp]

  type 'r t = 'r info String.Map.t [@@deriving sexp]

  let find t x = Map.find t x |> Option.map ~f:(fun i -> i.tm)
  let empty = String.Map.empty

  let regvar t x = match find t x with
    | Some (Regvar (r, t)) -> Some (r, t)
    | _ -> None

  let regvar_v t x = match find t x with
    | Some (Regvar_v r) -> Some r
    | _ -> None

  let imm t x = match find t x with
    | Some (Imm (i, t)) -> Some (i, t)
    | _ -> None

  let single t x = match find t x with
    | Some (Single s) -> Some s
    | _ -> None

  let double t x = match find t x with
    | Some (Double d) -> Some d
    | _ -> None

  let sym t x = match find t x with
    | Some (Sym (s, o)) -> Some (s, o)
    | _ -> None

  let label t x = match find t x with
    | Some (Label l) -> Some l
    | _ -> None

  let bool t x = match find t x with
    | Some (Bool b) -> Some b
    | _ -> None

  let table t x = match find t x with
    | Some (Table (d, tbl)) -> Some (d, tbl)
    | _ -> None

  let callargs t x = match find t x with
    | Some (Callargs rs) -> Some rs
    | _ -> None
end

module Rule(C : Context_intf.S) = struct
  open C.Syntax

  type ('r, 'i) callback = 'r Subst.t -> 'i list option C.t
  type ('r, 'i) t = Pattern.toplevel * ('r, 'i) callback list

  let (=>) pre post = pre, [post]
  let (=>*) pre post = pre, post

  let (let*!) x f = match x with
    | None -> !!None
    | Some x -> f x

  let (!!!) x = !!(Some x)
  let guard x = if x then Some () else None
  let try_ x fs = C.List.find_map fs ~f:((|>) x)
end
