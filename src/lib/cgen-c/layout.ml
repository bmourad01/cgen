open Core
open Monads.Std
open Regular.Std
open Type

module Vec = Cgen_containers.Vec
module E = Monad.Result.Error
module T = Cgen.Type
module TE = Type_env
module D = Data_model

module Bitfield = struct
  type t = {
    storage        : int;
    offset         : int;
    width          : int;
    access_storage : int;
    access_bits    : int;
  } [@@deriving bin_io, compare, equal, hash, sexp]

  let create ~storage ~offset ~width ~access_storage ~access_bits =
    {storage; offset; width; access_storage; access_bits}

  let storage t = t.storage
  let offset t = t.offset
  let width t = t.width
  let access_storage t = t.access_storage
  let access_bits t = t.access_bits
end

type bitfield = Bitfield.t [@@deriving bin_io, compare, equal, hash, sexp]

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
  | Texpr.Econst (Expr.Cint {value; _}) -> Cgen.Bv.to_int value
  | _ -> failwith "non-constant array size"

open E.Let
open E.Syntax

(* Size and alignment (in bytes) of a field type. *)
let rec field_size_align gamma dm : Texpr.ty -> (int * int) E.t = function
  | Tbase {base = Bvoid; _} -> Or_error.error_string "void field"
  | Tbase {base; _} ->
    let b = basic_of_base dm base in
    let s = T.sizeof_basic b / 8 in
    Ok (s, s)
  | Tptr _ ->
    let s = D.pointer_bytes dm in
    Ok (s, s)
  | Tarray {size = None; _} -> Or_error.error_string "incomplete array field"
  | Tarray {elem; size = Some e; _} ->
    let+ es, ea = field_size_align gamma dm elem in
    array_count e * es, ea
  | Tnamed {kind = `enum; _} ->
    let s = D.int_bytes dm in
    Ok (s, s)
  | Tnamed {kind = `typedef; name; _} ->
    Or_error.errorf "unresolved typedef %S in field" name
  | Tnamed {kind = #compound; name; _} ->
    begin match gamma name with
      | Some sa -> Ok sa
      | None -> Or_error.errorf "compound %S not laid out" name
    end
  | Tfun _ -> Or_error.error_string "function type field"

(* The width in bits of a bit-field's storage unit (its declared type). *)
let bits_of_type dm : Texpr.ty -> int E.t = function
  | Tbase {base; _} -> Ok (T.sizeof_basic (basic_of_base dm base))
  | Tnamed {kind = `enum; _} -> Ok (D.int_bits dm)
  | _ -> Or_error.error_string "bit field on non-integer type"

let round_up n a = ((n + a - 1) / a) * a

let access_unit ~storage ~offset ~width ~ub ~is_member_byte =
  let x_lo = (storage * 8 + offset) / 8 in
  let x_hi = (storage * 8 + offset + width - 1) / 8 in
  let touches lo hi = Seq.exists (Seq.range lo hi) ~f:is_member_byte in
  if not (touches storage (storage + ub)) then storage, ub else
    let try_w w =
      let a = x_lo / w * w in
      if w <= ub
      && x_hi < a + w
      && a + w <= storage + ub
      && not (touches a (a + w))
      then Some (a, w) else None in
    List.find_map [1; 2; 4; 8] ~f:try_w |>
    Option.value ~default:(storage, ub)

let layout_struct gamma dm fields =
  let rec go p align offs members bits = function
    | [] ->
      let align = max align 1 in
      let size = round_up p (align * 8) / 8 in
      Ok (size, align, offs, members, List.rev bits)
    | (f : Tdecl.field) :: rest -> match f.fbits with
      | None ->
        let* fs, fa = field_size_align gamma dm f.fty in
        let p = round_up p (fa * 8) in
        let offs = Map.set offs ~key:f.fname ~data:(p / 8) in
        go (p + fs * 8) (max align fa) offs ((p / 8, fs) :: members) bits rest
      | Some 0 when String.is_empty f.fname ->
        let* u = bits_of_type dm f.fty in
        go (round_up p u) align offs members bits rest
      | Some 0 ->
        Or_error.errorf
          "named bit field '%s' cannot have zero width"
          f.fname
      | Some w ->
        let* u = bits_of_type dm f.fty in
        let* () =
          if w < 0 || w > u then
            Or_error.errorf
              "bit field '%s' width %d out of range"
              f.fname w
          else Ok () in
        let p = if p mod u + w > u then round_up p u else p in
        let storage = p / u * (u / 8) in
        let offset = p - storage * 8 in
        let bits =
          if String.is_empty f.fname then bits
          else (f.fname, storage, offset, w, u / 8) :: bits in
        go (p + w) (max align (u / 8)) offs members bits rest in
  let* size, align, offs, members, bits =
    go 0 1 String.Map.empty [] [] fields in
  let is_member_byte byte =
    List.exists members ~f:(fun (mo, ms) ->
        mo <= byte && byte < mo + ms) in
  let bfs =
    List.fold bits ~init:String.Map.empty
      ~f:(fun bfs (name, storage, offset, width, ub) ->
          let access_storage, ab =
            access_unit ~storage ~offset ~width ~ub ~is_member_byte in
          let data =
            Bitfield.create ~storage ~offset ~width
              ~access_storage ~access_bits:(ab * 8) in
          Map.set bfs ~key:name ~data) in
  Ok (size, align, offs, bfs)

let layout_union gamma dm fields =
  let rec go size align offs bfs = function
    | [] ->
      let align = max align 1 in
      Ok ((if size = 0 then 0 else round_up size align), align, offs, bfs)
    | (f : Tdecl.field) :: rest -> match f.fbits with
      | None ->
        let* fs, fa = field_size_align gamma dm f.fty in
        go (max size fs) (max align fa)
          (Map.set offs ~key:f.fname ~data:0) bfs rest
      | Some 0 when String.is_empty f.fname ->
        go size align offs bfs rest
      | Some 0 ->
        Or_error.errorf
          "named bit field %S cannot have zero width"
          f.fname
      | Some w ->
        let* u = bits_of_type dm f.fty in
        let* () =
          if w < 0 || w > u
          then Or_error.errorf "bit field %S width %d out of range" f.fname w
          else Ok () in
        let bfs =
          if String.is_empty f.fname then bfs else
            let data =
              Bitfield.create ~storage:0 ~offset:0 ~width:w
                ~access_storage:0 ~access_bits:u in
            Map.set bfs ~key:f.fname ~data in
        go (max size (u / 8)) (max align (u / 8)) offs bfs rest in
  go 0 1 String.Map.empty String.Map.empty fields

let layout_compound dm ~gamma ~kind fields = match kind with
  | `struct_ -> layout_struct gamma dm fields
  | `union   -> layout_union gamma dm fields

type 'a map = 'a Map.M(String).t
[@@deriving bin_io, compare, equal, hash, sexp]

type t = {
  dmodel  : D.t;              (* data model *)
  tenv    : TE.t;             (* typing environment *)
  sizes   : (int * int) map;  (* (size, align) in bytes, per compound tag *)
  offsets : int map map;      (* field offset environment (per type) *)
  bfields : bitfield map map; (* bitfield environment (per type) *)
} [@@deriving bin_io, compare, equal, hash, sexp]

let empty ~dmodel = {
  dmodel;
  tenv = TE.empty;
  sizes = String.Map.empty;
  offsets = String.Map.empty;
  bfields = String.Map.empty;
}

let tenv t = t.tenv
let dmodel t = t.dmodel

(* Compute and record the layout of a complete compound. Nested compounds
   must already be present in [t.sizes]. *)
let put_compound t ~name ~kind fields =
  let gamma s = Map.find t.sizes s in
  let+ size, align, offs, bfs = layout_compound t.dmodel ~gamma ~kind fields in
  let sizes = Map.set t.sizes ~key:name ~data:(size, align) in
  let offsets = Map.set t.offsets ~key:name ~data:offs in
  let bfields = Map.set t.bfields ~key:name ~data:bfs in
  {t with sizes; offsets; bfields}

let create dmodel tenv =
  let compounds =
    TE.tags tenv |> Seq.filter_map ~f:(function
        | name, TE.Tcompound {kind; fields = (_ :: _ as fields)} ->
          Some (name, kind, fields)
        | _ -> None) |> Seq.to_list in
  let* defs =
    Seq.of_list compounds |>
    Seq.map ~f:(fun (n, k, f) -> n, (k, f)) |>
    String.Map.of_sequence |> function
    | `Duplicate_key n ->
      Or_error.errorf "duplicate compound type '%s'" n
    | `Ok defs -> !!defs in
  let rec refs_of_ty : Texpr.ty -> string list = function
    | Tarray {elem; _} -> refs_of_ty elem
    | Tnamed {kind = #compound; name; _} -> [name]
    | _ -> [] in
  (* Post-order DFS so a nested compound is laid out before its container. *)
  let visited = String.Hash_set.create () in
  let order = Vec.create () in
  let rec visit name =
    Hash_set.strict_add visited name |>
    Or_error.iter ~f:(fun () ->
        Map.find defs name |>
        Option.iter ~f:(fun (_, fields) ->
            List.iter fields ~f:(fun (f : Tdecl.field) ->
                List.iter (refs_of_ty f.fty) ~f:visit));
        Vec.push order name) in
  List.iter compounds ~f:(fun (n, _, _) -> visit n);
  let+ t =
    Vec.to_sequence_mutable order |>
    Seq.filter_map ~f:(fun n ->
        Map.find defs n |>
        Option.map ~f:(fun (k, f) -> n, k, f)) |>
    E.Seq.fold
      ~init:(empty ~dmodel)
      ~f:(fun acc (name, kind, fields) ->
          put_compound acc ~name ~kind fields) in
  {t with tenv}

(* Tenv-mutating forwarders.

   For tags, we additionally extend the layout maps when the
   tag is a complete struct/union.

   Enums and forward declarations leave the layout maps untouched.
*)

let add_tag t ~name tag =
  let* tenv = TE.add_tag t.tenv ~name tag in
  match tag with
  | TE.Tenum _ | TE.Tcompound {fields = []; _} ->
    Ok {t with tenv}
  | TE.Tcompound {kind; fields} ->
    put_compound {t with tenv} ~name ~kind fields

let add_enum_element t ~name ~tag ~value =
  let+ tenv = TE.add_enum_element t.tenv ~name ~tag ~value in
  {t with tenv}

let add_typedef t ~name ty =
  let+ tenv = TE.add_typedef t.tenv ~name ty in
  {t with tenv}

let add_func t ~name ty =
  let+ tenv = TE.add_func t.tenv ~name ty in
  {t with tenv}

let add_global t ~name ty =
  let+ tenv = TE.add_global t.tenv ~name ty in
  {t with tenv}

let add_local t ~name ty =
  {t with tenv = TE.add_local t.tenv ~name ty}

let strict_add_local t ~name ty =
  let+ tenv = TE.strict_add_local t.tenv ~name ty in
  {t with tenv}

let push_scope t = {t with tenv = TE.push_scope t.tenv}

let rec size_align dm sizes = function
  | Tbase {base = Bvoid; _} ->
    Or_error.error_string "sizeof void"
  | Tbase {base; _} ->
    let s = T.sizeof_basic (basic_of_base dm base) / 8 in
    Ok (s, s)
  | Tptr _ ->
    let s = D.pointer_bytes dm in
    Ok (s, s)
  | Tarray {size = None; _} ->
    Or_error.error_string "sizeof incomplete array"
  | Tarray {elem; size = Some e; _} ->
    let+ esz, eal = size_align dm sizes elem in
    array_count e * esz, eal
  | Tnamed {kind = `enum; _} ->
    let s = D.int_bytes dm in
    Ok (s, s)
  | Tnamed {kind = `typedef; name; _} ->
    Or_error.errorf "unresolved typedef %S" name
  | Tnamed {kind = #compound; name; _} ->
    begin match Map.find sizes name with
      | None -> Or_error.errorf "compound %S not laid out" name
      | Some sa -> Ok sa
    end
  | Tfun _ -> Or_error.error_string "sizeof function type"

let sizeof t ty = size_align t.dmodel t.sizes ty >>| fst
let alignof t ty = size_align t.dmodel t.sizes ty >>| snd

let offsetof t ~tag ~field = match Map.find t.offsets tag with
  | None -> Or_error.errorf "unknown tag %S" tag
  | Some m -> match Map.find m field with
    | Some off -> Ok off
    | None ->
      let bfs =
        Map.find t.bfields tag |>
        Option.value ~default:String.Map.empty in
      if Map.mem bfs field
      then Or_error.errorf "'%s.%s' is a bit field" tag field
      else Or_error.errorf "unknown field '%s.%s'" tag field

let bitfield_info t ~tag ~field = match Map.find t.bfields tag with
  | None -> Or_error.errorf "unknown tag %S" tag
  | Some m -> match Map.find m field with
    | None -> Or_error.errorf "'%s.%s' is not a bit field" tag field
    | Some bf -> Ok bf
