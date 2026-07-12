(* Lowering a typed C translation unit (`Tcunit.t`) to Structured IR.

   Each function definition becomes a `Structured.Func`; globals become
   `Virtual.data`; struct/union definitions become named IR types. Locals
   and parameters are given stack slots (reads/writes become loads/stores;
   the backend's slot-promotion passes lift scalars back into registers),
   and parameters are stored into their slots in a prologue.
*)

open Core

module Bv = Cgen_utils.Bv
module IT = Cgen.Type
module Ctx = Cgen.Context
module S = Cgen.Structured
module V = Cgen.Virtual
module L = Cgen.Linkage
module Dict = Cgen.Dict
module Target = Cgen.Target
module E = Lower_expr
module Smap = E.Smap
module Bf = Layout.Bitfield

open Ctx.Syntax

let (let@) f x = f x [@@ocaml.warning "-32"]

let visibility_of = function
  | Attr.Default -> L.Default
  | Attr.Hidden -> L.Hidden
  | Attr.Internal -> L.Internal
  | Attr.Protected -> L.Protected

let linkage_of ~attrs (l : Tdecl.linkage) =
  let export = match l with
    | Lextern -> true
    | Lstatic -> false in
  let visibility =
    Option.value_map (Attr.visibility attrs)
      ~default:L.Default ~f:visibility_of in
  L.create
    ~section:(Attr.section attrs)
    ~weak:(Attr.weak attrs)
    ~visibility
    ~export ()

let alias_data ~name ~linkage ~attrs ~target =
  let dict = Dict.set Dict.empty V.Data.Tag.linkage (linkage_of ~attrs linkage) in
  V.Data.create_alias ~name ~target ~dict ()

(* {1 Body traversal} *)

let rec collect_labels acc (s : Tstmt.t) = match s with
  | Slabel {name; body} -> collect_labels (name :: acc) body
  | Sblock items ->
    List.fold items ~init:acc ~f:(fun acc -> function
        | Tstmt.Bstmt s -> collect_labels acc s
        | Tstmt.Bdecl _ -> acc)
  | Sif {then_; else_; _} ->
    let acc = collect_labels acc then_ in
    Option.fold else_ ~init:acc ~f:collect_labels
  | Swhile {body; _}
  | Sdowhile {body; _}
  | Sfor {body; _}
  | Sswitch {body; _}
  | Scase {body; _}
  | Sdefault body
    -> collect_labels acc body
  | Sgoto _
  | Sgotoind _
  | Sbreak
  | Scontinue
  | Sreturn _
  | Sinstr _
    -> acc

(* {1 Functions} *)

let lower_fundef
    layout
    ~strings
    ~nstr
    ~name
    ~(params : Tdecl.param list)
    ~(ret : Texpr.ty)
    ~body
    ~variadic
    ~linkage
    ~attrs
    ~labaddrs =
  (* Parameters are allocated up front, function-wide. Block-scoped locals
     are allocated lazily as they come into scope during statement lowering,
     so that two declarations sharing a name (such as a local shadowing a
     global) get distinct slots and resolve per their C scope. *)
  let param_specs =
    Sequence.of_list params |>
    Sequence.map ~f:(fun (p : Tdecl.param) -> p.pname, p.pty) in
  let* param_entries =
    Ctx.Seq.map param_specs ~f:(Tuple2.uncurry @@ E.alloc_slot layout) in
  let param_slots =
    Sequence.map param_entries ~f:fst |>
    Sequence.to_list |> Smap.of_alist_overwrite in
  let param_slot_list = Sequence.to_list @@ Sequence.map param_entries ~f:snd in
  (* Accumulates every local slot allocated while lowering the body. *)
  let local_slots = ref [] in
  (* One incoming-argument variable per parameter, stored into its slot. *)
  let* args =
    Ctx.List.map params ~f:(fun (p : Tdecl.param) ->
        let+ av = Ctx.Var.fresh in
        p, av) in
  (* Map all C labels to fresh cgen counterparts. *)
  let* labels =
    collect_labels [] body |>
    List.dedup_and_sort ~compare:String.compare |>
    Ctx.List.fold ~init:Smap.empty ~f:(fun acc n ->
        let+ l = Ctx.Label.fresh in
        Smap.set acc ~key:n ~data:l) in
  (* Initial environments. *)
  let e : E.env = {layout; slots = param_slots; strings; nstr} in
  let c : Lower_stmt.t = {
    e; labels; slots = local_slots;
    brk = `structured;
    case_labels = [];
    default_label = None;
    labaddrs;
  } in
  (* The core lowering. *)
  let+ body_s = Lower_stmt.lower_stmt c body in
  let slot_list = param_slot_list @ List.rev !local_slots in
  (* Prepend the prologue to the body; this consists of storing
     the parameters to their corresponding slots. *)
  let body_with_prologue =
    List.fold_right args ~init:body_s ~f:(fun ((p : Tdecl.param), av) acc ->
        let arg = Lower_type.arg_of layout p.pty in
        let dst = Smap.find_exn param_slots p.pname in
        `seq (`store (arg, `var av, `var dst), acc)) in
  let body = S.Stmt.normalize body_with_prologue in
  let func_args =
    List.map args ~f:(fun ((p : Tdecl.param), av) ->
        av, Lower_type.arg_of layout p.pty) in
  let fn = S.Func.create ~name ~args:func_args ~slots:slot_list ~body () in
  let fn = S.Func.with_tag fn V.Func.Tag.linkage (linkage_of ~attrs linkage) in
  let fn = if variadic then S.Func.with_tag fn V.Func.Tag.variadic () else fn in
  match Lower_type.ret_of layout ret with
  | Some r -> S.Func.with_tag fn V.Func.Tag.return r
  | None -> fn

(* {1 Globals} *)

let scalar_imm layout ty = E.imm_of_basic (fst (Lower_type.scalar layout ty))

let intern_string layout strings nstr s =
  E.intern_string {
    layout;
    slots = Smap.empty;
    strings;
    nstr;
  } s

(* The byte offset of an address constant as a signed integer. The evaluator
   masks it to pointer width, so reinterpret the top bit as the sign. *)
let addr_offset layout (off : Bv.t) =
  let bits = Data_model.pointer_bits (Layout.dmodel layout) in
  let z = Bv.to_bigint off in
  let half = Z.shift_left Z.one (bits - 1) in
  Z.to_int (if Z.lt z half then z else Z.sub z (Z.shift_left Z.one bits))

(* A constant scalar initializer as a data element, via the §6.6 ¶7
   initializer-constant evaluator: integer/float literals, string literals
   (decayed to the address of an interned copy), null pointers, and address
   constants ([&obj], [&arr[i]], [&s.field], and those +/- an integer). *)
let const_elt layout ~strings ~nstr (e : Texpr.t) =
  let+? v = Eval.const (Eval.create_init layout) e in
  match v with
  | Eval.Vint bv          -> `int (bv, scalar_imm layout e.ty)
  | Eval.Vnull            -> `int (Bv.zero, scalar_imm layout e.ty)
  | Eval.Vfloat f         -> `float f
  | Eval.Vdouble d        -> `double d
  | Eval.Vstring s        -> `sym (intern_string layout strings nstr s, 0)
  | Eval.Vaddr {sym; off} -> `sym (sym, addr_offset layout off)

let tenv layout = Layout.tenv layout

let array_elem layout ty : Texpr.ty =
  match Type_env.normalize (tenv layout) ty with
  | Tarray {elem; _} -> elem
  | _ -> failwith "lower: array initializer for a non-array type"

let is_field name (f : Tdecl.field) = String.(f.fname = name)

let field_type layout ~tag ~field : Texpr.ty =
  match Type_env.find_tag (tenv layout) tag with
  | Some Tcompound {fields = Some fields; _} ->
    begin match List.find fields ~f:(is_field field) with
      | Some f -> f.fty
      | None -> failwithf "lower: no field %S in %S" field tag ()
    end
  | _ -> failwithf "lower: %S is not a compound type" tag ()

(* Pad the (reversed) element list with zeroes from `cur` up to `target`. *)
let pad_to acc cur target =
  if target > cur
  then (`zero (target - cur) :: acc), target
  else acc, cur

let bitfield_type_bytes layout ~tag ~field =
  let ft = field_type layout ~tag ~field in
  let t, _ = Lower_type.scalar layout ft in
  IT.sizeof_basic t / 8

let init_int layout ~what = function
  | Texpr.Isingle e ->
    Eval.create_init layout |>
    Fn.flip Eval.const e |>
    Or_error.bind ~f:(function
        | Eval.Vint bv -> Ok bv
        | _ -> Or_error.errorf "lower: non-integer %s initializer" what)
  | _ -> Or_error.errorf "lower: aggregate %s initializer" what

(* OR a value of `width` bits at `bitoff` into a storage-unit accumulator. *)
let splice_bits ~little ~unit_bytes ~bitoff ~width ~acc v =
  let module B = (val Bv.modular (unit_bytes * 8)) in
  let bitoff = if little then bitoff else unit_bytes * 8 - bitoff - width in
  let mask = B.(pred (one lsl int width)) in
  B.(acc lor ((v land mask) lsl int bitoff))

let imm_of_bytes : int -> IT.imm = function
  | 1 -> `i8
  | 2 -> `i16
  | 4 -> `i32
  | 8 -> `i64
  | n -> failwithf "lower: bad storage-unit size %d" n ()

let imm_bytes (i : IT.imm) = IT.sizeof_basic (i :> IT.basic) / 8

(* Coalesce a set of bit-field byte offsets into aligned power-of-two integer
   cells (largest alignment first), reading each byte's value from `bf_byte`. *)
let coalesce_bytes ~little bf_byte bytes =
  let rec group = function
    | [] -> []
    | x :: xs ->
      let rec span hi = function
        | y :: ys when y = hi -> span (hi + 1) ys
        | r -> hi, r in
      let hi, rest = span (x + 1) xs in
      (x, hi) :: group rest in
  List.concat_map (group (Set.to_list bytes)) ~f:(fun (lo, hi) ->
      let rec go p k =
        if p >= hi then k [] else
          (* Find the largest alignment `w` that fits `p` *)
          let a = ref 8 and w = ref 0 in
          while !a > 0 && !w = 0 do
            if p mod !a = 0 && p + !a <= hi
            then w := !a else a := !a lsr 1
          done;
          let w = !w in
          assert (w > 0);
          let module Bw = (val Bv.modular (w * 8)) in
          let v = Sequence.fold (Sequence.range 0 w) ~init:Bw.zero ~f:(fun a j ->
              let byte =
                Hashtbl.find bf_byte (p + j) |>
                Option.value ~default:0 in
              (* Byte `p + j` lands at the lowest address on little-endian
                 (least-significant), at the highest on big-endian, since the
                 assembler orders the emitted integer's bytes. *)
              let sh = if little then 8 * j else 8 * (w - 1 - j) in
              Bw.(a lor (int byte lsl int sh))) in
          go (p + w) (fun acc -> k ((p, imm_of_bytes w, v) :: acc))  in
      go lo Fn.id)

(* Emit the data elements for a constant initializer. *)
let rec emit_init
    layout
    ~strings
    ~nstr
    ~base
    ~(ty : Texpr.ty)
    (init : Texpr.init)
    (acc : V.Data.elt list) =
  let*? size = Layout.sizeof layout ty in
  let endpos = base + size in
  let* acc, cur = match init with
    | Isingle e when Lower_type.is_aggregate layout ty ->
      (* A character array initialized by a string literal: emit the bytes
         inline, the NUL and any remaining bytes fall to the tail padding. *)
      begin match e.node with
        | Econst Cstr s ->
          let len = String.length s in
          (* `string_array_init` in the elaborator guarantees the literal
             fits (a fixed bound requires `n >= len`), so the bytes never
             overrun the element and the `pad_to` below stays non-negative.
             Guard that invariant in case a future initializer path reaches
             here without the check. *)
          assert (len <= size);
          let acc = if len = 0 then acc else `string s :: acc in
          !!(acc, base + len)
        | _ -> Ctx.failf "lower: unsupported aggregate initializer" ()
      end
    | Isingle e ->
      let+ elt = const_elt layout ~strings ~nstr e in
      elt :: acc, endpos
    | Iarray inits ->
      let elem = array_elem layout ty in
      let*? esz = Layout.sizeof layout elem in
      emit_array layout ~strings ~nstr ~base ~elem ~esz inits 0 acc
    | Istruct fields ->
      emit_fields layout
        ~strings ~nstr ~base
        ~tag:(Lower_type.compound_tag_exn layout ty)
        fields acc base
    | Iunion {name; init} ->
      let fty =
        field_type layout
          ~tag:(Lower_type.compound_tag_exn layout ty)
          ~field:name in
      emit_init layout ~strings ~nstr ~base ~ty:fty init acc
    | Ioverlay _ ->
      (* This should be rejected by the earlier constant-expression check. *)
      failwith "lower: overlay in a static initializer" in
  !!(pad_to acc cur endpos)

and emit_array layout ~strings ~nstr ~base ~elem ~esz inits i acc =
  match inits with
  | [] -> !!(acc, base + i * esz)
  | init :: rest ->
    let* acc, _ =
      emit_init layout ~strings ~nstr ~base:(base + i * esz) ~ty:elem init acc in
    emit_array layout ~strings ~nstr ~base ~elem ~esz rest (i + 1) acc

(* Emit a struct initializer's data image. *)
and emit_fields layout ~strings ~nstr ~base ~tag fields acc cur =
  let* little = Ctx.target >>| Target.little in
  let unit_bytes = Int.Table.create () in
  List.iter fields ~f:(fun (field, _) ->
      match Layout.bitfield_info layout ~tag ~field with
      | Ok bf ->
        let b = bitfield_type_bytes layout ~tag ~field in
        Hashtbl.update unit_bytes (Bf.storage bf)
          ~f:(Option.value_map ~default:b ~f:(max b))
      | Error _ -> ());
  let unit_val = Int.Table.create () in
  let bf_byte = Int.Table.create () in
  let rec classify members = function
    | [] -> !!members
    | (field, finit) :: rest ->
      match Layout.bitfield_info layout ~tag ~field with
      | Ok bf ->
        let*? v = init_int layout ~what:"bit field" finit in
        let storage = Bf.storage bf in
        let off = Bf.offset bf and w = Bf.width bf in
        let ub = Hashtbl.find_exn unit_bytes storage in
        Hashtbl.update unit_val storage ~f:(fun cur ->
            splice_bits ~little ~unit_bytes:ub ~bitoff:off ~width:w
              ~acc:(Option.value cur ~default:Bv.zero) v);
        let z = Bv.to_bigint v and base_bit = storage * 8 + off in
        for i = 0 to w - 1 do
          if Z.testbit z i then
            let q = if little then base_bit + i else base_bit + (w - 1 - i) in
            let sub = if little then q mod 8 else 7 - (q mod 8) in
            Hashtbl.update bf_byte (q / 8) ~f:(fun c ->
                Option.value c ~default:0 lor (1 lsl sub))
        done;
        classify members rest
      | Error _ ->
        let*? off = Layout.offsetof layout ~tag ~field in
        let fty = field_type layout ~tag ~field in
        let*? sz = Layout.sizeof layout fty in
        classify ((off, sz, fty, finit) :: members) rest in
  let* members = classify [] fields in
  let overlaps storage ub =
    List.exists members ~f:(fun (moff, msz, _, _) ->
        moff < storage + ub && storage < moff + msz) in
  let unit_cells, split_bytes =
    Hashtbl.fold unit_bytes ~init:([], Int.Set.empty)
      ~f:(fun ~key:storage ~data:ub (cells, split) ->
          if overlaps storage ub then
            let split =
              Sequence.range storage (storage + ub) |>
              Sequence.filter ~f:(Hashtbl.mem bf_byte) |>
              Sequence.fold ~init:split ~f:Set.add in
            cells, split
          else
            let v =
              Hashtbl.find unit_val storage |>
              Option.value ~default:Bv.zero in
            let cell = storage, `Int (imm_of_bytes ub, v, ub) in
            (cell :: cells), split) in
  let byte_cells =
    coalesce_bytes ~little bf_byte split_bytes |>
    List.map ~f:(fun (off, imm, v) ->
        off, `Int (imm, v, imm_bytes imm)) in
  let member_cells =
    List.map members ~f:(fun (off, _, fty, init) -> off, `Mem (fty, init)) in
  let cells =
    List.sort
      (unit_cells @ byte_cells @ member_cells)
      ~compare:(fun (a, _) (b, _) -> Int.compare a b) in
  let rec emit acc cur = function
    | [] -> !!(acc, cur)
    | (off, cell) :: rest ->
      let acc, _cur = pad_to acc cur (base + off) in
      match cell with
      | `Int (imm, v, w) ->
        emit (`int (v, imm) :: acc) (base + off + w) rest
      | `Mem (fty, init) ->
        let* acc, cur =
          emit_init layout ~strings ~nstr ~base:(base + off) ~ty:fty init acc in
        emit acc cur rest in
  emit acc cur cells

let lower_global
    layout
    ~strings
    ~nstr
    ~name
    ~(ty : Texpr.ty)
    ~(init : Texpr.init option)
    ~linkage
    ~attrs =
  let* elts = match init with
    | None ->
      let+? size = Layout.sizeof layout ty in
      [`zero size]
    | Some init ->
      let+ acc, _ = emit_init layout ~strings ~nstr ~base:0 ~ty init [] in
      List.rev acc in
  let dict = Dict.set Dict.empty V.Data.Tag.linkage (linkage_of ~attrs linkage) in
  let dict =
    if Type.Cv.is_const (Type.cv_of ty)
    then Dict.set dict V.Data.Tag.const ()
    else dict in
  (* An `aligned`/`_Alignas` over-alignment on the object. Globals, unlike
     stack slots, have no realignment constraint, so it is applied as-is. *)
  let dict = match Attr.alignment attrs with
    | Some n when n > 0 -> Dict.set dict V.Data.Tag.align n
    | _ -> dict in
  Ctx.lift_err @@ V.Data.create ~dict ~name ~elts ()

(* {1 Translation unit} *)

let module_ ~name (tc : Tcunit.t) =
  let layout = Tcunit.layout tc in
  let strings = String.Table.create () in
  let nstr = ref 0 in
  let classify (d : Tdecl.t) = match d with
    | Dfundef {name; params; ret; body; linkage; variadic; labaddrs; attrs; _} ->
      let+ fn =
        lower_fundef layout ~strings ~nstr ~name ~params ~ret ~body
          ~variadic ~linkage ~attrs ~labaddrs in
      `Fun fn
    | Dglobal {name; ty; init; linkage; attrs; _} ->
      begin match Attr.alias attrs with
        | Some target -> !!(`Data (alias_data ~name ~linkage ~attrs ~target))
        | None ->
          let+ data =
            lower_global layout ~strings ~nstr ~name ~ty ~init ~linkage ~attrs in
          `Data data
      end
    | Dcompound {kind; tag; fields} ->
      let*? named = Lower_type.named_of_compound layout ~kind ~tag ~fields in
      !!(`Type named)
    (* A prototype carrying `alias` becomes a function alias; other prototypes
       and externs emit nothing. *)
    | Dfundecl {name; linkage; attrs; _} ->
      begin match Attr.alias attrs with
        | Some target -> !!(`Data (alias_data ~name ~linkage ~attrs ~target))
        | None -> !!`None
      end
    | Dextern _ -> !!`None in
  let* items = Ctx.List.map (Tcunit.decls tc) ~f:classify in
  let funs = List.filter_map items ~f:(function `Fun f -> Some f | _ -> None) in
  let data = List.filter_map items ~f:(function `Data d -> Some d | _ -> None) in
  let typs = List.filter_map items ~f:(function `Type t -> Some t | _ -> None) in
  (* Private data for interned string literals (NUL-terminated). *)
  let+ str_data = Hashtbl.to_alist strings |> Ctx.List.map ~f:(fun (s, sym) ->
      Ctx.lift_err @@ V.Data.create ~name:sym ~elts:[`string s; `zero 1] ()) in
  S.Module.create ~name ~typs ~data:(data @ str_data) ~funs ()
