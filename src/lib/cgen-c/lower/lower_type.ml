open Core
open Monads.Std

module E = Monad.Result.Error
module IT = Cgen.Type

open E.Let

let is_signed : Type.sign -> bool = function
  | Ssigned -> true
  | Sunsigned -> false

let imm_of_bits : int -> IT.imm = function
  | 8 -> `i8
  | 16 -> `i16
  | 32 -> `i32
  | 64 -> `i64
  | n -> failwithf "lower: unsupported integer width of %d bits" n ()

let pointer_imm dm = imm_of_bits (Data_model.pointer_bits dm)

(* The IR basic type and integer-signedness of a C base type. *)
let basic_of_base dm base =
  let i bits = (imm_of_bits bits :> IT.basic) in
  match (base : Type.base) with
  | Bvoid -> failwith "lower: void is not a scalar value"
  | Bbool -> i Data_model.bool_bits, false
  | Bchar -> i Data_model.char_bits, Data_model.char_signed dm
  | Bint Ichar s -> i Data_model.char_bits, is_signed s
  | Bint Ishort s -> i Data_model.short_bits, is_signed s
  | Bint Iint s -> i (Data_model.int_bits dm), is_signed s
  | Bint Ilong s -> i (Data_model.long_bits dm), is_signed s
  | Bint Ilonglong s -> i Data_model.long_long_bits, is_signed s
  | Bfloat Ffloat -> (`f32 :> IT.basic), false
  | Bfloat Fdouble -> (`f64 :> IT.basic), false

let norm layout ty = Type_env.normalize (Layout.tenv layout) ty

(* A struct/union/array occupies memory and is never loaded as a scalar.

   Such an lvalue yields its address rather than a loaded value.
*)
let is_aggregate layout ty = match (norm layout ty : Texpr.ty) with
  | Tnamed {kind = `struct_ | `union; _} | Tarray _ -> true
  | _ -> false

(* The IR basic type, with signedness of a scalar C type.

   Pointers, decayed arrays, and function designators are pointer-width
   integers. `enum` is `int`.
*)
let scalar layout ty =
  let dm = Layout.dmodel layout in
  match (norm layout ty : Texpr.ty) with
  | Tbase {base; _} -> basic_of_base dm base
  | Tptr _ | Tfun _ | Tarray _ ->
    (pointer_imm dm :> IT.basic), false
  | Tnamed {kind = `enum; _} ->
    (imm_of_bits (Data_model.int_bits dm) :> IT.basic), true
  | Tnamed {kind = `struct_ | `union; name; _} ->
    failwithf "lower: %S is an aggregate, not a scalar" name ()
  | Tnamed {kind = `typedef; name; _} ->
    failwithf "lower: typedef %S should have been normalized away" name ()

(* The compound tag of a struct/union type, if any. *)
let compound_tag layout ty = match (norm layout ty : Texpr.ty) with
  | Tnamed {kind = `struct_ | `union; name; _} -> Some name
  | _ -> None

(* Elaboration should have caught these errors, so fail loudly
   when we need to resolve compound types. *)
let compound_tag_exn layout ty = match compound_tag layout ty with
  | Some tag -> tag
  | None ->
    let s = Format.asprintf "%a" (Type.pp_with Texpr.pp) (norm layout ty) in
    failwithf "lower: expected a struct/union type, got '%s'" s ()

(* The IR argument type: a named compound for struct/union, otherwise a
   scalar basic type. *)
let arg_of layout ty = match compound_tag layout ty with
  | None -> (fst (scalar layout ty) :> IT.arg)
  | Some tag -> `name tag

let ret_of_basic (b : IT.basic) ~signed : IT.ret = match b with
  | `i8 when signed -> `si8
  | `i16 when signed -> `si16
  | `i32 when signed -> `si32
  | _ -> (b :> IT.ret)

(* The IR return type: `None` for void, a named compound for struct/union,
   otherwise a (sign-aware) scalar. *)
let ret_of layout ty : IT.ret option =
  match (norm layout ty : Texpr.ty) with
  | Tbase {base = Bvoid; _} -> None
  | Tnamed {kind = `struct_ | `union; name; _} -> Some (`name name)
  | _ ->
    let b, signed = scalar layout ty in
    Some (ret_of_basic b ~signed)

(* An IR struct/union element from a non-bitfield C field, peeling array
   dimensions into a repeat count. *)
let field_elt layout (f : Tdecl.field) =
  let rec peel ty : Texpr.ty =
    match (norm layout ty : Texpr.ty) with
    | Tarray {elem; _} -> peel elem
    | t -> t in
  let elem = peel f.fty in
  let+ count = match (norm layout f.fty : Texpr.ty) with
    | Tarray _ ->
      let+ sf = Layout.sizeof layout f.fty
      and+ se = Layout.sizeof layout elem in
      if se = 0 then 0 else sf / se
    | _ -> Ok 1 in
  match elem with
  | Tnamed {kind = #Type.compound; name; _} -> `name (name, count)
  | _ -> `elt (fst (scalar layout elem), count)

let round_up n a = (n + a - 1) / a * a

let int_elt_of_bytes n : IT.basic = match n * 8 with
  | 8 -> `i8
  | 16 -> `i16
  | 32 -> `i32
  | 64 -> `i64
  | _ -> failwithf "lower: bad bit-field storage-unit size %d" n ()

(* The width in bits of a bit-field's declared-type storage unit. *)
let bitfield_unit_bits layout ty = IT.sizeof_basic (fst (scalar layout ty))

(* A struct's storage as a list of non-overlapping cells in offset order,
   mirroring `Layout.layout_struct`. *)
let struct_cells layout fields =
  let rec go p units members = function
    | [] -> Ok (List.rev units, List.rev members)
    | (f : Tdecl.field) :: rest -> match f.fbits with
      | None ->
        let* fs = Layout.sizeof layout f.fty in
        let* fa = Layout.alignof layout f.fty in
        let p = round_up p (fa * 8) in
        let* elt = field_elt layout f in
        go (p + fs * 8) units ((p / 8, fa, fs, elt) :: members) rest
      | Some 0 -> go (round_up p (bitfield_unit_bits layout f.fty)) units members rest
      | Some w ->
        let u = bitfield_unit_bits layout f.fty in
        let p = if p mod u + w > u then round_up p u else p in
        let storage = p / u * (u / 8) in
        let ub = u / 8 in
        let units = match units with
          | (s, _) :: _ when s = storage -> units
          | _ -> (storage, ub) :: units in
        go (p + w) units members rest in
  go 0 [] [] fields

(* Build a named IR compound type from an elaborated compound definition.

   The IR has no bitfields, so the type just describes the underlying storage,
   keeping its size, alignment, and ABI classification correct.

   Field offsets come separately from `Layout`.
*)
let named_of_compound layout ~kind ~tag ~fields =
  let+ elts = match kind with
    | `union ->
      (* Every union member starts at offset 0, so there is no packing to
         resolve: emit each member's element (a bit field as its unit). *)
      let flush u acc = match u with
        | None -> acc
        | Some basic -> `elt (basic, 1) :: acc in
      let rec go acc u = function
        | [] -> Ok (List.rev (flush u acc))
        | (f : Tdecl.field) :: rest -> match f.fbits with
          | None ->
            let* elt = field_elt layout f in
            go (elt :: flush u acc) None rest
          | Some 0 -> go (flush u acc) None rest
          | Some _ ->
            let basic = fst (scalar layout f.fty) in
            go (flush u acc) (Some basic) rest in
      go [] None fields
    | `struct_ ->
      let* units, members = struct_cells layout fields in
      let contained (off, _, size, _) =
        List.exists units ~f:(fun (us, ub) -> us <= off && off + size <= us + ub) in
      let cells =
        List.filter members ~f:(Fn.non contained)
        @ List.map units ~f:(fun (us, ub) ->
            us, ub, ub, `elt (int_elt_of_bytes ub, 1))
        |> List.sort ~compare:(fun (a, _, _, _) (b, _, _, _) -> Int.compare a b) in
      (* Emit cells in order, inserting explicit byte padding only where a gap
         cannot be reproduced by the next element's own alignment (so ordinary
         structs are unaffected). *)
      let rec emit acc running = function
        | [] -> Ok (List.rev acc)
        | (off, align, size, elt) :: rest ->
          let acc =
            if round_up running align < off
            then elt :: `elt (`i8, off - running) :: acc
            else elt :: acc in
          emit acc (off + size) rest in
      emit [] 0 cells in
  let t = match kind with
    | `struct_ -> `struct_ (tag, None, elts)
    | `union -> `union (tag, None, elts) in
  (t : IT.named)
