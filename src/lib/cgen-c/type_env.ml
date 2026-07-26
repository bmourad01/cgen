open Core
open Type

module Rrb = Cgen_containers.Rrb
module Bv = Cgen_utils.Bv
module Vec = Cgen_containers.Vec
module E = Cgen_utils.Monads.Error
module T = Cgen.Type
module D = Data_model

type enum_element = {
  ecname  : string;
  ectag   : string;
  ecvalue : int64;
} [@@deriving bin_io, compare, equal, hash, sexp]

module Enum_element = struct
  type t = enum_element [@@deriving bin_io, compare, equal, hash, sexp]
  let name c = c.ecname
  let tag c = c.ectag
  let value c = c.ecvalue
end

type tag =
  | Tenum of (string * int64) list
  | Tcompound of {
      kind   : Type.compound;
      fields : Tdecl.field list option;  (* None: incomplete (forward-declared) *)
      attrs  : Attr.set;
    }
[@@deriving bin_io, compare, equal, hash, sexp]

module Smap = Cgen_containers.Champ.Make(String)

type 'a map = 'a Smap.t [@@deriving bin_io, compare, equal, hash, sexp]

let empty_map = Smap.empty

type tagid = int [@@deriving bin_io, compare, equal, hash, sexp]

(* Intermediate data of a bitfield, as we're computing the
   layout of a struct *)
type bfunit = {
  bfname    : string; (* field name *)
  bfstorage : int;    (* byte offset of the storage unit *)
  bfoffset  : int;    (* bit offset of the field *)
  bfwidth   : int;    (* width in bits *)
  bfsize    : int;    (* full size in bytes *)
}

module Bitfield = struct
  type t = {
    storage        : int;
    offset         : int;
    width          : int;
    access_storage : int;
    access_bits    : int;
    bytewise       : bool;
  } [@@deriving bin_io, compare, equal, hash, sexp]

  let create
      ?(bytewise = false)
      ~storage
      ~offset
      ~width
      ~access_storage
      ~access_bits
      () =
    {storage; offset; width; access_storage; access_bits; bytewise}

  let create_from_bfunit
      ?(bytewise = false)
      u
      ~access_storage
      ~access_bits = {
    storage = u.bfstorage;
    offset = u.bfoffset;
    width = u.bfwidth;
    access_storage;
    access_bits;
    bytewise;
  }

  let storage t = t.storage
  let offset t = t.offset
  let width t = t.width
  let access_storage t = t.access_storage
  let access_bits t = t.access_bits
  let bytewise t = t.bytewise
end

type bitfield = Bitfield.t [@@deriving bin_io, compare, equal, hash, sexp]

(* NB: `lenv` and `tscopes` are stacks of scopes, because names
   defined in a deeper block scope are allowed to shadow those of
   the same name in a shallower one.

   Tags are split into a persistent store and a lexical scope stack.
   `tdefs`/`tnames` are indexed by identity and never popped, because
   the lowering (which has no notion of scope) must see every tag
   globally.
*)
type t = {
  tdefs   : tag Rrb.t;         (* tag info, by identity *)
  tnames  : string Rrb.t;      (* display name, by identity *)
  tids    : tagid map;         (* identity, by display name (persistent) *)
  tscopes : tagid map list;    (* per-scope: identify by source tag name *)
  eenv    : enum_element map;  (* enum elements *)
  denv    : Texpr.ty map;      (* typedefs *)
  fenv    : Texpr.ty map;      (* functions *)
  venv    : Texpr.ty map;      (* globals *)
  lenv    : Texpr.ty map list; (* locals and params *)
  dmodel  : D.t;               (* data model *)
  sizes   : (int * int) map;   (* (size, align) in bytes, per compound tag *)
  offsets : int map map;       (* field offset environment (per type) *)
  bfields : bitfield map map;  (* bitfield environment (per type) *)
} [@@deriving bin_io, compare, equal, hash, sexp]

let empty ~dmodel = {
  tdefs   = Rrb.empty;
  tnames  = Rrb.empty;
  tids    = empty_map;
  tscopes = [empty_map];
  eenv    = empty_map;
  denv    = empty_map;
  fenv    = empty_map;
  venv    = empty_map;
  lenv    = [empty_map];
  dmodel;
  sizes   = empty_map;
  offsets = empty_map;
  bfields = empty_map;
}

(* All four maps below share the ordinary-identifier namespace per C99. *)
let in_ordinary env name =
  Smap.mem env.eenv name ||
  Smap.mem env.denv name ||
  Smap.mem env.fenv name ||
  Smap.mem env.venv name

let same_compound_kind (a : Type.compound) (b : Type.compound) = match a, b with
  | `struct_, `struct_ | `union, `union -> true
  | _ -> false

let cur_tscope env = match env.tscopes with
  | m :: _ -> m
  | [] -> failwith "Type_env: empty tag scope stack"

let with_cur_tscope env m = match env.tscopes with
  | _ :: rest -> {env with tscopes = m :: rest}
  | [] -> failwith "Type_env: empty tag scope stack"

let fresh_display env name id =
  if Smap.mem env.tids name then Printf.sprintf "%s.%d" name id else name

(* {1 Layout computation} *)

let basic_of_bits = function
  | 8 -> `i8
  | 16 -> `i16
  | 32 -> `i32
  | 64 -> `i64
  | n -> failwithf "unsupported integer width: %d" n ()

let basic_of_base dm = function
  | Bvoid -> invalid_arg "void has no representation"
  | Bbool -> basic_of_bits D.bool_bits
  | Bchar -> basic_of_bits D.char_bits
  | Bint (Ichar _) -> basic_of_bits D.char_bits
  | Bint (Ishort _) -> basic_of_bits D.short_bits
  | Bint (Iint _) -> basic_of_bits (D.int_bits dm)
  | Bint (Ilong _) -> basic_of_bits (D.long_bits dm)
  | Bint (Ilonglong _) -> basic_of_bits D.long_long_bits
  | Bfloat Ffloat -> `f32
  | Bfloat Fdouble -> `f64

let pointer_basic dm = basic_of_bits (D.pointer_bits dm) [@@ocaml.warning "-32"]

let array_count e = match e.Texpr.node with
  | Texpr.Econst (Expr.Cint {value; _}) -> Bv.to_int value
  | _ -> failwith "non-constant array size"

open E.Let
open E.Syntax

(* Size and alignment (in bytes) of a type. *)
let rec size_align ~what gamma dm : Texpr.ty -> (int * int) E.t = function
  | Tbase {base = Bvoid; _} ->
    Or_error.errorf "void %s" what
  | Tbase {base; _} ->
    let b = basic_of_base dm base in
    let s = T.sizeof_basic b / 8 in
    Ok (s, s)
  | Tptr _ ->
    let s = D.pointer_bytes dm in
    Ok (s, s)
  | Tarray {size = None; _} ->
    Or_error.error_string "incomplete array %s"
  | Tarray {elem; size = Some e; _} ->
    let+ es, ea = size_align ~what gamma dm elem in
    array_count e * es, ea
  | Tnamed {kind = `enum; _} ->
    let s = D.int_bytes dm in
    Ok (s, s)
  | Tnamed {kind = `typedef; name; _} ->
    Or_error.errorf "unresolved typedef '%s' in %s" name what
  | Tnamed {kind = #compound; name; _} ->
    begin match gamma name with
      | Some sa -> Ok sa
      | None -> Or_error.errorf "compound '%s' not laid out" name
    end
  | Tfun _ -> Or_error.errorf "function type %s" what

(* The width in bits of a bit-field's storage unit (its declared type). *)
let bits_of_type dm : Texpr.ty -> int E.t = function
  | Tbase {base; _} -> Ok (T.sizeof_basic (basic_of_base dm base))
  | Tnamed {kind = `enum; _} -> Ok (D.int_bits dm)
  | _ -> Or_error.error_string "bit field on non-integer type"

let round_up n a = ((n + a - 1) / a) * a

let field_align ~packed fa (f : Tdecl.field) =
  let base = if packed then 1 else fa in
  match Attr.alignment f.fattrs with
  | Some n when n > 0 -> max base n
  | _ -> base

let aggr_align attrs align = match Attr.alignment attrs with
  | Some n when n > 0 -> max align n
  | _ -> align

(* Derive the integer used to read/write a bit field at run time.

   `Some (a, w)`: a single `w`-byte integer at byte offset `a` that
   contains all of the field's bytes and stays within the object
   (`a + w <= u.bfsize`). An access overlapping another member's bytes
   is fine, since the store is a read-modify-write that leaves them intact.

   `None`: no single in-bounds access covers the field (a `packed` field
   that straddles its unit), so it must be accessed byte by byte.
*)
let access_bfunit u ~size ~is_member_byte =
  let x_lo = (u.bfstorage * 8 + u.bfoffset) / 8 in
  let x_hi = (u.bfstorage * 8 + u.bfoffset + u.bfwidth - 1) / 8 in
  let touches lo hi = Sequence.(exists (range lo hi) ~f:is_member_byte) in
  let covers a w = a <= x_lo && x_hi < a + w && a + w <= size in
  (* Prefer the natural declared-type unit when it fits and is member-free. *)
  if covers u.bfstorage u.bfsize
  && not (touches u.bfstorage (u.bfstorage + u.bfsize))
  then Some (u.bfstorage, u.bfsize)
  else with_return @@ fun {return} ->
    (* Otherwise narrow to the smallest covering, member-free unit. *)
    for i = 0 to 3 do
      let w = 1 lsl i in
      let a = (x_lo / w) * w in
      if w <= u.bfsize
      && covers a w
      && not (touches a (a + w))
      then return @@ Some (a, w)
    done;
    (* No member-free unit, so use the natural unit if it still covers
       the field in bounds (read-modify-write keeps the overlap intact).
       Otherwise, the field straddles and is accessed byte by byte. *)
    Option.some_if (covers u.bfstorage u.bfsize) (u.bfstorage, u.bfsize)

(* Check that the bitfield fits in the declared type. *)
let check_bitfield_width dm name ty w =
  let* u = bits_of_type dm ty in
  if w < 0 || w > u then
    Or_error.errorf
      "bit field '%s' width %d out of range (expected between %d and %d)"
      name w 0 u
  else Ok u

let layout_struct gamma dm ~attrs fields =
  let packed = Attr.packed attrs in
  let rec go p align offs members bits = function
    | [] ->
      let align = aggr_align attrs (max align 1) in
      let size = round_up p (align * 8) / 8 in
      Ok (size, align, offs, members, List.rev bits)
    | (f : Tdecl.field) :: rest -> match f.fbits with
      | None ->
        (* Non-bitfield. This is the easy case. *)
        let* fs, fa = size_align ~what:"field" gamma dm f.fty in
        let fa = field_align ~packed fa f in
        let p = round_up p (fa * 8) in
        let offs = Smap.set offs ~key:f.fname ~data:(p / 8) in
        go (p + fs * 8) (max align fa) offs ((p / 8, fs) :: members) bits rest
      | Some 0 when String.is_empty f.fname ->
        (* Simply advance to next unit. *)
        let* u = bits_of_type dm f.fty in
        let p = if packed then p else round_up p u in
        go p align offs members bits rest
      | Some 0 ->
        Or_error.errorf
          "named bit field '%s' cannot have zero width"
          f.fname
      | Some w ->
        let* u = check_bitfield_width dm f.fname f.fty w in
        (* Under `packed`, a bit field is placed at the next bit with no
           unit-boundary padding. Otherwise, it must fit within one unit. *)
        let p = if packed || p mod u + w <= u then p else round_up p u in
        let bfstorage = (p / u) * (u / 8) in
        let bfoffset = p - bfstorage * 8 in
        let bits = if String.is_empty f.fname then bits else {
            bfname = f.fname;
            bfstorage;
            bfoffset;
            bfwidth = w;
            bfsize = u / 8;
          } :: bits in
        let fa = if packed then 1 else u / 8 in
        go (p + w) (max align fa) offs members bits rest in
  let* size, align, offs, members, bits =
    go 0 1 Smap.empty [] [] fields in
  let is_member_byte byte =
    List.exists members ~f:(fun (mo, ms) ->
        mo <= byte && byte < mo + ms) in
  let* bfs = List.fold_result bits ~init:Smap.empty ~f:(fun bfs u ->
      match access_bfunit u ~size ~is_member_byte with
      | Some (access_storage, ab) ->
        let access_bits = ab * 8 in
        let data = Bitfield.create_from_bfunit u ~access_storage ~access_bits in
        Ok (Smap.set bfs ~key:u.bfname ~data)
      | None ->
        (* No single in-bounds access covers the field; it is read and
           written one byte at a time (see `bytewise`), which assembles
           the covered bytes into an i64, so its span cannot exceed 8. *)
        let p = u.bfstorage * 8 + u.bfoffset in
        let span = (p + u.bfwidth - 1) / 8 - p / 8 + 1 in
        if span > 8 then
          Or_error.errorf
            "packed bit field '%s' spans %d bytes, at most 8 are supported"
            u.bfname span
        else
          let data =
            Bitfield.create_from_bfunit u
              ~access_storage:0
              ~access_bits:0
              ~bytewise:true in
          Ok (Smap.set bfs ~key:u.bfname ~data)) in
  Ok (size, align, offs, bfs)

let layout_union gamma dm ~attrs fields =
  let packed = Attr.packed attrs in
  let rec go size align offs bfs = function
    | [] ->
      let align = aggr_align attrs (max align 1) in
      Ok ((if size = 0 then 0 else round_up size align), align, offs, bfs)
    | (f : Tdecl.field) :: rest -> match f.fbits with
      | None ->
        let* fs, fa = size_align ~what:"field" gamma dm f.fty in
        let fa = field_align ~packed fa f in
        go (max size fs) (max align fa)
          (Smap.set offs ~key:f.fname ~data:0) bfs rest
      | Some 0 when String.is_empty f.fname ->
        go size align offs bfs rest
      | Some 0 ->
        Or_error.errorf
          "named bit field '%s' cannot have zero width"
          f.fname
      | Some w ->
        let* u = check_bitfield_width dm f.fname f.fty w in
        let bfs =
          if String.is_empty f.fname then bfs else
            let data =
              Bitfield.create
                ~storage:0
                ~offset:0
                ~width:w
                ~access_storage:0
                ~access_bits:u
                () in
            Smap.set bfs ~key:f.fname ~data in
        let size = max size (u / 8)
        and align = max align (u / 8) in
        go size align offs bfs rest in
  go 0 1 Smap.empty Smap.empty fields

let layout_compound dm ~gamma ~kind ~attrs fields = match kind with
  | `struct_ -> layout_struct gamma dm ~attrs fields
  | `union   -> layout_union gamma dm ~attrs fields

(* Compute and record the layout of a complete compound. Nested compounds
   must already be present in [t.sizes]. *)
let put_compound t ~name ~kind ~attrs fields =
  let gamma s = Smap.find t.sizes s in
  let+ size, align, offs, bfs = layout_compound t.dmodel ~gamma ~kind ~attrs fields in
  let sizes = Smap.set t.sizes ~key:name ~data:(size, align) in
  let offsets = Smap.set t.offsets ~key:name ~data:offs in
  let bfields = Smap.set t.bfields ~key:name ~data:bfs in
  {t with sizes; offsets; bfields}

(* {1 Tag/name registration} *)

(* Register a tag definition (name and scope only), returning the updated
   environment and the display name the tag was given (which the caller
   records in the elaborated type). *)
let add_tag_tenv env ~name info =
  match Smap.find (cur_tscope env) name with
  | Some id ->
    (* When we have a redeclaration in the same scope, we either complete
       a forward declaration, accept a redundant re-forward-declaration,
       or reject an incompatible redefinition. The identity is preserved. *)
    let disp = Rrb.get_exn env.tnames id in
    let store info = {env with tdefs = Rrb.set env.tdefs id info} in
    begin match Rrb.get_exn env.tdefs id, info with
      | Tcompound {kind = ek; fields = None; _}, Tcompound {kind = nk; _}
        when same_compound_kind ek nk -> Ok (store info, disp)
      | Tcompound {fields = None; _}, _ ->
        Or_error.errorf "tag '%s' redeclared as a different kind" name
      | _, Tcompound {fields = None; _} -> Ok (env, disp)
      | _ -> Or_error.errorf "tag '%s' already defined" name
    end
  | None ->
    let id = Rrb.length env.tdefs in
    let disp = fresh_display env name id in
    let env = {
      env with
      tdefs = Rrb.snoc env.tdefs info;
      tnames = Rrb.snoc env.tnames disp;
      tids = Smap.set env.tids ~key:disp ~data:id;
    } in
    let env =
      with_cur_tscope env @@
      Smap.set (cur_tscope env) ~key:name ~data:id in
    Ok (env, disp)

(* Register a tag definition. For a complete struct/union this also computes
   and stores its layout in the same step, so the tag and its layout are never
   out of step. Incomplete compounds and enums update only the tenv. *)
let add_tag env ~name info =
  let* env, disp = add_tag_tenv env ~name info in
  match info with
  | Tenum _ | Tcompound {fields = None; _} -> Ok (env, disp)
  | Tcompound {kind; fields = Some fields; attrs} ->
    let+ env = put_compound env ~name:disp ~kind ~attrs fields in
    env, disp

let add_enum_element env ~name ~tag ~value =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else
    let data = {ecname = name; ectag = tag; ecvalue = value} in
    Ok {env with eenv = Smap.set env.eenv ~key:name ~data}

let add_typedef env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else Ok {env with denv = Smap.set env.denv ~key:name ~data:ty}

let add_func env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else Ok {env with fenv = Smap.set env.fenv ~key:name ~data:ty}

let add_global env ~name ty =
  if in_ordinary env name
  then Or_error.errorf "identifier '%s' already declared" name
  else Ok {env with venv = Smap.set env.venv ~key:name ~data:ty}

let add_local env ~name ty = match env.lenv with
  | [] -> failwith "Type_env.add_local: no scope on the stack"
  | m :: rest -> {env with lenv = Smap.set m ~key:name ~data:ty :: rest}

let strict_add_local env ~name ty = match env.lenv with
  | [] -> failwith "Type_env.strict_add_local: no scope on the stack"
  | m :: rest -> match Smap.add m ~key:name ~data:ty with
    | `Duplicate -> Or_error.errorf "redeclaration of '%s'" name
    | `Ok m -> Ok {env with lenv = m :: rest}

let push_scope env = {
  env with
  lenv = empty_map :: env.lenv;
  tscopes = empty_map :: env.tscopes;
}

let exit_block ~saved env = {
  env with
  eenv = saved.eenv;
  denv = saved.denv;
  lenv = saved.lenv;
  tscopes = saved.tscopes;
}

let resolve_tag env name =
  List.find_map env.tscopes ~f:(fun m -> Smap.find m name) |>
  Option.map ~f:(Rrb.get_exn env.tnames)

let find_tag env disp = Option.bind (Smap.find env.tids disp) ~f:(Rrb.get env.tdefs)
let find_enum_element env name = Smap.find env.eenv name
let find_typedef env name = Smap.find env.denv name
let find_func env name = Smap.find env.fenv name
let find_global env name = Smap.find env.venv name
let find_local env name = List.find_map env.lenv ~f:(Fn.flip Smap.find name)

let has_tag env disp = Smap.mem env.tids disp
let has_enum_element env name = Smap.mem env.eenv name
let has_typedef env name = Smap.mem env.denv name
let has_func env name = Smap.mem env.fenv name
let has_global env name = Smap.mem env.venv name
let has_local env name = List.exists env.lenv ~f:(Fn.flip Smap.mem name)

let tags env =
  Rrb.to_sequence env.tdefs |>
  Sequence.mapi ~f:(fun id tag -> Rrb.get_exn env.tnames id, tag)

let enum_elements env = Smap.to_sequence env.eenv
let typedefs env = Smap.to_sequence env.denv
let funcs env = Smap.to_sequence env.fenv
let globals env = Smap.to_sequence env.venv

let locals env =
  let init = empty_map in
  Smap.to_sequence @@ List.fold env.lenv ~init ~f:(fun init m ->
      Smap.foldi m ~init ~f:(fun ~key ~data m ->
          match Smap.add m ~key ~data with
          | `Duplicate -> m
          | `Ok m -> m))

let is_tag_complete env disp = match find_tag env disp with
  | None | Some (Tenum [] | Tcompound {fields = None; _}) -> false
  | Some _ -> true

(* Resolve typedefs in a type, returning a `Texpr.ty` with no `Tnamed`
   typedef nodes.

   Outer cv-qualifiers compose, e.g. a `const` on the typedef name
   unions with whatever the underlying type has. Struct/union/enum
   tags are not expanded.

   This function is idempotent.
*)
let normalize env ty =
  let rec go : Texpr.ty -> Texpr.ty = function
    | Tbase _ as t -> t
    | Tnamed {kind = `typedef; name; cv} as t ->
      find_typedef env name |>
      Option.value_map ~default:t ~f:(fun underlying ->
          let underlying = go underlying in
          let combined = Type.Cv.combine cv (Type.cv_of underlying) in
          Type.with_cv combined underlying)
    | Tnamed _ as t -> t
    | Tptr {pointee; restrict; cv} ->
      Type.ptr ~cv ~restrict (go pointee)
    | Tarray {elem; size = None; cv; restrict; static_} ->
      Type.array ~cv ~restrict ~static_ (go elem)
    | Tarray {elem; size = Some _ as size; cv; restrict; static_} ->
      Type.array ~cv ~restrict ~static_ ?size @@ go elem
    | Tfun {result; params = None; _} ->
      Type.fun_kr (go result)
    | Tfun {result; params = Some ps; variadic} ->
      let params =
        List.map ps ~f:(fun (p : Texpr.t Type.param) ->
            Type.{p with ptype = go p.ptype}) in
      Type.fun_ ~result:(go result) ~params ~variadic () in
  go ty

let rec incomplete_object_type env ty = match normalize env ty with
  | Tnamed {kind = #Type.compound; name; _} ->
    if is_tag_complete env name then None else Some name
  | Tarray {elem; _} -> incomplete_object_type env elem
  | _ -> None

(* {1 Layout queries} *)

let dmodel t = t.dmodel

(* The alignment of a type, computed without its array sizes, so it succeeds
   for a variably-modified (VLA) type. An array's alignment is that of its
   element, independent of the (possibly non-constant) length.

   `_Alignof` does not evaluate the operand (§6.5.3.4), so the size is never
   needed.
*)
let rec align_of dm sizes = function
  | Tbase {base = Bvoid; _} -> Or_error.error_string "alignof void"
  | Tbase {base; _} -> Ok (T.sizeof_basic (basic_of_base dm base) / 8)
  | Tptr _ -> Ok (D.pointer_bytes dm)
  | Tarray {elem; _} -> align_of dm sizes elem
  | Tnamed {kind = `enum; _} -> Ok (D.int_bytes dm)
  | Tnamed {kind = `typedef; name; _} -> Or_error.errorf "unresolved typedef %S" name
  | Tnamed {kind = #compound; name; _} ->
    begin match Smap.find sizes name with
      | None -> Or_error.errorf "compound %S not laid out" name
      | Some (_, a) -> Ok a
    end
  | Tfun _ -> Or_error.error_string "alignof function type"

let sizeof t ty =
  size_align
    ~what:"sizeof"
    (Smap.find t.sizes)
    t.dmodel
    (normalize t ty)
  >>| fst

let alignof t ty = align_of t.dmodel t.sizes (normalize t ty)

let offsetof t ~tag ~field = match Smap.find t.offsets tag with
  | None -> Or_error.errorf "unknown tag %S" tag
  | Some m -> match Smap.find m field with
    | Some off -> Ok off
    | None ->
      let bfs =
        Smap.find t.bfields tag |>
        Option.value ~default:Smap.empty in
      if Smap.mem bfs field
      then Or_error.errorf "'%s.%s' is a bit field" tag field
      else Or_error.errorf "unknown field '%s.%s'" tag field

let bitfield_info t ~tag ~field = match Smap.find t.bfields tag with
  | None -> Or_error.errorf "unknown tag %S" tag
  | Some m -> match Smap.find m field with
    | None -> Or_error.errorf "'%s.%s' is not a bit field" tag field
    | Some bf -> Ok bf
