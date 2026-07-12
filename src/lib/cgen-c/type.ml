open Core

type sign =
  | Ssigned
  | Sunsigned
[@@deriving bin_io, compare, equal, hash, sexp]

type ity =
  | Ichar of sign
  | Ishort of sign
  | Iint of sign
  | Ilong of sign
  | Ilonglong of sign
[@@deriving bin_io, compare, equal, hash, sexp]

let ity_sign = function
  | Ichar s
  | Ishort s
  | Iint s
  | Ilong s
  | Ilonglong s -> s

type fty =
  | Ffloat
  | Fdouble
[@@deriving bin_io, compare, equal, hash, sexp]

type base =
  | Bvoid
  | Bbool
  | Bchar
  | Bint of ity
  | Bfloat of fty
[@@deriving bin_io, compare, equal, hash, sexp]

module Cv = struct
  type t = int [@@deriving bin_io, compare, equal, hash]

  let combine = (lor)

  let empty = 0b00
  let mask = 0b11 [@@ocaml.warning "-32"]

  let const = 0b01
  let volatile = 0b10
  let const_volatile = combine const volatile

  let is_const t = (t land const) <> empty
  let is_volatile t = (t land volatile) <> empty
  let is_const_volatile t = t = const_volatile

  let sexp_of_t t : Sexp.t =
    if t = empty then Atom ""
    else if t = const then Atom "const"
    else if t = volatile then Atom "volatile"
    else if t = const_volatile then Atom "const volatile"
    else failwithf "Type.Cv.sexp_of_t: unexpected cv-qualifier %d" t ()

  let t_of_sexp : Sexp.t -> t = function
    | Atom "" -> empty
    | Atom "const" -> const
    | Atom "volatile" -> volatile
    | Atom ("const volatile" | "volatile const") -> const_volatile
    | _ -> failwith "Type.Cv.t_of_sexp: unexpected sexp"

  let pp ppf t = Format.fprintf ppf "%a" Sexp.pp (sexp_of_t t)
end

type cv = Cv.t [@@deriving bin_io, compare, equal, hash, sexp]

type compound = [
  | `struct_
  | `union
] [@@deriving bin_io, compare, equal, hash, sexp]

type tag = [
  | compound
  | `enum
] [@@deriving bin_io, compare, equal, hash, sexp]

type named = [
  | tag
  | `typedef
] [@@deriving bin_io, compare, equal, hash, sexp]

type 'e t =
  | Tbase of {
      base : base;
      cv   : cv;
    }
  | Tptr of {
      pointee  : 'e t;
      restrict : bool;
      cv       : cv;
    }
  | Tarray of {
      elem     : 'e t;
      size     : 'e option;
      cv       : cv;
      restrict : bool;
      (** Only meaningful on a parameter: the type qualifiers ([cv]) and
          [restrict] inside its brackets (C99 §6.7.6.3), which qualify the
          pointer it decays to. *)
      static_  : bool;
      (** Only meaningful on a parameter: the [static] in [a\[static n\]]
          (C99 §6.7.6.3), asserting the argument points to at least [size]
          elements. It has no home on the decayed pointer type, so it is
          dropped there; cgen does not otherwise use it. *)
    }
  | Tnamed of {
      kind : named;
      name : string;
      cv   : cv;
    }
  | Tfun of {
      result   : 'e t;
      params   : 'e param list option;
      variadic : bool;
    }

and 'e param = {
  pname : string option;
  ptype : 'e t;
} [@@deriving bin_io, compare, equal, hash, sexp]

let void ?(cv= Cv.empty) () = Tbase {base = Bvoid; cv}
let bool_ ?(cv= Cv.empty) () = Tbase {base = Bbool; cv}
let plain_char_ ?(cv= Cv.empty) () = Tbase {base = Bchar; cv}

let char_ ?(cv= Cv.empty) sign =
  Tbase {base = Bint (Ichar sign); cv}

let int_ ?(cv= Cv.empty) ?(sign = Ssigned) () =
  Tbase {base = Bint (Iint sign); cv}

let short_ ?(cv= Cv.empty) ?(sign = Ssigned) () =
  Tbase {base = Bint (Ishort sign); cv}

let long_ ?(cv= Cv.empty) ?(sign = Ssigned) () =
  Tbase {base = Bint (Ilong sign); cv}

let longlong_ ?(cv= Cv.empty) ?(sign = Ssigned) () =
  Tbase {base = Bint (Ilonglong sign); cv}

let float_ ?(cv= Cv.empty) () = Tbase {base = Bfloat Ffloat; cv}
let double_ ?(cv= Cv.empty) () = Tbase {base = Bfloat Fdouble; cv}

let ptr ?(cv= Cv.empty) ?(restrict = false) pointee =
  Tptr {pointee; restrict; cv}

let array ?(cv= Cv.empty) ?(restrict = false) ?(static_ = false) ?size elem =
  Tarray {elem; size; cv; restrict; static_}

let struct_  ?(cv= Cv.empty) name = Tnamed {kind = `struct_; name; cv}
let union_   ?(cv= Cv.empty) name = Tnamed {kind = `union;   name; cv}
let enum_    ?(cv= Cv.empty) name = Tnamed {kind = `enum;    name; cv}
let typedef_ ?(cv= Cv.empty) name = Tnamed {kind = `typedef; name; cv}

let fun_ ~result ~params ?(variadic = false) () =
  Tfun {result; params = Some params; variadic}

let fun_kr result = Tfun {result; params = None; variadic = false}

let is_void = function
  | Tbase {base = Bvoid; _} -> true
  | _ -> false

let is_integer = function
  | Tbase {base = Bbool | Bchar | Bint _; _} -> true
  | Tnamed {kind = `enum; _} -> true
  | _ -> false

let is_floating = function
  | Tbase {base = Bfloat _; _} -> true
  | _ -> false

let is_arithmetic t = is_integer t || is_floating t

let is_pointer = function
  | Tptr _ -> true
  | _ -> false

let is_scalar t = is_arithmetic t || is_pointer t

let is_array = function
  | Tarray _ -> true
  | _ -> false

let is_function = function
  | Tfun _ -> true
  | _ -> false

let is_compound = function
  | Tnamed {kind = #compound; _} -> true
  | _ -> false

let cv_of = function
  | Tbase  r -> r.cv
  | Tptr   r -> r.cv
  | Tarray r -> r.cv
  | Tnamed r -> r.cv
  | Tfun   _ -> Cv.empty

let with_cv cv = function
  | Tbase  r -> Tbase  {r with cv}
  | Tptr   r -> Tptr   {r with cv}
  | Tarray r -> Tarray {r with cv}
  | Tnamed r -> Tnamed {r with cv}
  | Tfun   _ as t -> t

let unqualified t = with_cv Cv.empty t

(* Pretty printing *)

let pp_sign ppf = function
  | Ssigned   -> Format.pp_print_string ppf "signed"
  | Sunsigned -> Format.pp_print_string ppf "unsigned"

let pp_ity ppf = function
  | Ichar Ssigned       -> Format.pp_print_string ppf "signed char"
  | Ichar Sunsigned     -> Format.pp_print_string ppf "unsigned char"
  | Ishort Ssigned      -> Format.pp_print_string ppf "short"
  | Ishort Sunsigned    -> Format.pp_print_string ppf "unsigned short"
  | Iint Ssigned        -> Format.pp_print_string ppf "int"
  | Iint Sunsigned      -> Format.pp_print_string ppf "unsigned int"
  | Ilong Ssigned       -> Format.pp_print_string ppf "long"
  | Ilong Sunsigned     -> Format.pp_print_string ppf "unsigned long"
  | Ilonglong Ssigned   -> Format.pp_print_string ppf "long long"
  | Ilonglong Sunsigned -> Format.pp_print_string ppf "unsigned long long"

let pp_fty ppf = function
  | Ffloat  -> Format.pp_print_string ppf "float"
  | Fdouble -> Format.pp_print_string ppf "double"

let pp_base ppf = function
  | Bvoid    -> Format.pp_print_string ppf "void"
  | Bbool    -> Format.pp_print_string ppf "_Bool"
  | Bchar    -> Format.pp_print_string ppf "char"
  | Bint ity -> pp_ity ppf ity
  | Bfloat f -> pp_fty ppf f

(* Qualifiers for a specifier (in prefix form) *)
let pp_base_quals ppf cv =
  if Cv.is_const    cv then Format.pp_print_string ppf "const ";
  if Cv.is_volatile cv then Format.pp_print_string ppf "volatile "

(* Qualifiers on a pointer modifier (in suffix form) *)
let pp_ptr_quals ppf cv ~restrict =
  let const = Cv.is_const cv in
  let volatile = Cv.is_volatile cv in
  if const then Format.pp_print_string ppf " const";
  if volatile then Format.pp_print_string ppf " volatile";
  if restrict then Format.pp_print_string ppf " restrict";
  if const || volatile || restrict then Format.pp_print_char ppf ' '

let pp_tag_keyword ppf : tag -> unit = function
  | `struct_ -> Format.pp_print_string ppf "struct"
  | `union   -> Format.pp_print_string ppf "union"
  | `enum    -> Format.pp_print_string ppf "enum"

let rec pp_specifier : type e. Format.formatter -> e t -> unit = fun ppf -> function
  | Tbase {base; cv} ->
    pp_base_quals ppf cv;
    pp_base ppf base
  | Tnamed {kind = `typedef; name; cv} ->
    pp_base_quals ppf cv;
    Format.pp_print_string ppf name
  | Tnamed {kind = #tag as kind; name; cv} ->
    pp_base_quals ppf cv;
    pp_tag_keyword ppf kind;
    Format.pp_print_char ppf ' ';
    Format.pp_print_string ppf name
  | Tptr   {pointee; _} -> pp_specifier ppf pointee
  | Tarray {elem;    _} -> pp_specifier ppf elem
  | Tfun   {result;  _} -> pp_specifier ppf result

let declarator_is_empty (type e) (ty : e t) ~name =
  String.is_empty name && match ty with
  | Tbase _ | Tnamed _ -> true
  | Tptr _ | Tarray _ | Tfun _ -> false

(* Mutually recursive printers parameterized by an expression
   printer `pp_e`.

   Returns (`pp_named`, `pp_decl`):
   - `pp_named` emits the specifier and the declarator;
   - `pp_decl` emits the declarator only.
*)
let make_pp
  : type e.
    (Format.formatter -> e -> unit) ->
    (Format.formatter -> e t -> name:string -> unit) *
    (Format.formatter -> e t -> name:string -> unit) = fun pp_e ->
  let rec pp_named ppf ty ~name =
    pp_specifier ppf ty;
    if not (declarator_is_empty ty ~name)
    then Format.pp_print_char ppf ' ';
    pp_decl ppf ty ~name
  and pp_decl ppf ty ~name =
    let pp_name ppf =
      if not (String.is_empty name)
      then Format.pp_print_string ppf name in
    go ppf ~atom:false pp_name ty
  and go ppf ~atom pp_inner = function
    | Tbase _ | Tnamed _ -> pp_inner ppf
    | Tptr {pointee; cv; restrict} ->
      let pp_outer ppf =
        Format.pp_print_char ppf '*';
        pp_ptr_quals ppf cv ~restrict;
        pp_inner ppf in
      go ppf ~atom:true pp_outer pointee
    | Tarray {elem; size; cv; restrict; static_} ->
      let pp_outer ppf =
        if atom then Format.pp_print_char ppf '(';
        pp_inner ppf;
        if atom then Format.pp_print_char ppf ')';
        Format.pp_print_char ppf '[';
        let sp = ref false in
        let kw s =
          if !sp then Format.pp_print_char ppf ' ';
          Format.pp_print_string ppf s;
          sp := true in
        if Cv.is_const cv then kw "const";
        if Cv.is_volatile cv then kw "volatile";
        if restrict then kw "restrict";
        if static_ then kw "static";
        Option.iter size ~f:(fun e ->
            if !sp then Format.pp_print_char ppf ' ';
            pp_e ppf e);
        Format.pp_print_char ppf ']' in
      go ppf ~atom:false pp_outer elem
    | Tfun {result; params; variadic} ->
      let pp_outer ppf =
        if atom then Format.pp_print_char ppf '(';
        pp_inner ppf;
        if atom then Format.pp_print_char ppf ')';
        Format.pp_print_char ppf '(';
        pp_params ppf params variadic;
        Format.pp_print_char ppf ')' in
      go ppf ~atom:false pp_outer result
  and pp_params ppf params variadic = match params with
    | None -> ()
    | Some ps -> match ps, variadic with
      | [], false -> Format.pp_print_string ppf "void"
      | [], true  -> Format.pp_print_string ppf "..."
      | _ ->
        let pp_sep ppf () = Format.pp_print_string ppf ", " in
        Format.pp_print_list ~pp_sep (fun ppf p ->
            let name = Option.value p.pname ~default:"" in
            pp_named ppf p.ptype ~name) ppf ps;
        if variadic then Format.pp_print_string ppf ", ..." in
  pp_named, pp_decl

let pp_named_with pp_e ppf ty ~name =
  (fst (make_pp pp_e)) ppf ty ~name

let pp_declarator_with pp_e ppf ty ~name =
  (snd (make_pp pp_e)) ppf ty ~name

let pp_with pp_e ppf ty = pp_named_with pp_e ppf ty ~name:""
