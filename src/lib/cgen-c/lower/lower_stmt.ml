open Core

module Bv = Cgen_utils.Bv
module IT = Cgen.Type
module Ctx = Cgen.Context
module S = Cgen.Structured
module V = Cgen.Virtual
module E = Lower_expr
module Smap = E.Smap

open Ctx.Syntax

let (let@) f x = f x

(* Determines how a `break` statement is lowered.

   This is mainly here to deal with unstructured control flow
   in the case of "Duff's Device".
*)
type brk = [`structured | `goto of Cgen.Label.t]

(* Statement-lowering context. *)
type t = {
  e             : E.env;
  labels        : Cgen.Label.t E.map;
  slots         : V.slot list ref; (* lazily allocated slots *)
  brk           : brk;
  case_labels   : (Bv.t * Cgen.Label.t) list;
  default_label : Cgen.Label.t option;
  labaddrs      : string list;
}

let scalar_basic c ty = E.scalar_basic c.e ty

let cond_nonzero c ty (v : V.operand) : S.Stmt.cond =
  let b = scalar_basic c ty in
  `cmp (`ne b, v, E.zero_operand b)

let as_index (b : IT.basic) (v : V.operand) k = match v with
  | `var x -> k (`var x : V.Ctrl.swindex)
  | `sym (s, o) -> k (`sym (s, o))
  | _ ->
    let* x = E.fresh_var in
    let+ rest = k (`var x) in
    E.emit (`uop (x, `copy b, v)) rest

(* {1 Aggregate value materialization and stores} *)

let as_value c ty (operand : V.operand) k =
  match Lower_type.compound_tag c.e.layout ty with
  | None -> k operand
  | Some tag ->
    let* v = E.fresh_var in
    let+ rest = k (`var v) in
    E.emit (`load (v, `name tag, operand)) rest

let store c ty ~addr ~(value : V.operand) k =
  match Lower_type.compound_tag c.e.layout ty with
  | Some tag ->
    let* v = E.fresh_var in
    let+ rest = k () in
    S.Stmt.seq [
      `load (v, `name tag, value);
      `store (`name tag, `var v, addr);
      rest;
    ]
  | None ->
    let b = scalar_basic c ty in
    let+ rest = k () in
    E.emit (`store ((b :> IT.arg), value, addr)) rest

let store_value c ty ~addr ~(value : V.operand) k =
  let arg : IT.arg = match Lower_type.compound_tag c.e.layout ty with
    | Some tag -> `name tag
    | None -> (scalar_basic c ty :> IT.arg) in
  let+ rest = k () in
  E.emit (`store (arg, value, addr)) rest

let store_into_lval c ~(lval : Texpr.tlval) ~rhs k =
  match E.as_bitfield_lval c.e lval with
  | Some (inner, bf) ->
    let@ base = E.lower_lval c.e inner in
    let@ value = rhs in
    E.bitfield_store c.e ~base ~bf ~ty:lval.ty ~value k
  | None ->
    let@ addr = E.lower_lval c.e lval in
    let@ value = rhs in
    store c lval.ty ~addr ~value k

let store_result c ~(lval : Texpr.tlval) ~(value : V.operand) k =
  if Lower_type.is_aggregate c.e.layout lval.ty then
    let@ addr = E.lower_lval c.e lval in
    store_value c lval.ty ~addr ~value k
  else store_into_lval c ~lval ~rhs:(fun kk -> kk value) k

(* {1 Initializers} *)

let element_type c ty : Texpr.ty = match E.norm c.e ty with
  | Tarray {elem; _} -> elem
  | _ -> failwith "lower: array initializer for a non-array type"

let is_field name (f : Tdecl.field) = String.(f.fname = name)

let field_type c ~tag ~field : Texpr.ty =
  match Type_env.find_tag (Layout.tenv c.e.layout) tag with
  | Some (Tcompound {fields; _}) ->
    begin match List.find fields ~f:(is_field field) with
      | None -> failwithf "lower: no field %S in %S" field tag ()
      | Some f -> f.fty
    end
  | _ -> failwithf "lower: %S is not a compound type" tag ()

let rec lower_init c ~addr ~ty (init : Texpr.init) k = match init with
  | Isingle e ->
    let@ v = E.lower_rval c.e e in
    store c ty ~addr ~value:v k
  | Iarray inits ->
    let elem = element_type c ty in
    let*? esz = Layout.sizeof c.e.layout elem in
    lower_indexed c ~addr ~elem ~esz inits 0 k
  | Istruct fields ->
    let tag = Lower_type.compound_tag_exn c.e.layout ty in
    lower_fields c ~addr ~tag fields k
  | Iunion {name; init} ->
    let tag = Lower_type.compound_tag_exn c.e.layout ty in
    lower_init c ~addr ~ty:(field_type c ~tag ~field:name) init k
  | Ioverlay {base; over} ->
    (* Store the whole base value, then the overriding members on top. *)
    let@ v = E.lower_rval c.e base in
    let@ () = store c ty ~addr ~value:v in
    lower_init c ~addr ~ty over k

and lower_indexed c ~addr ~elem ~esz inits i k = match inits with
  | [] -> k ()
  | init :: rest ->
    let@ a = E.add_offset c.e addr (i * esz) in
    let@ () =  lower_init c ~addr:a ~ty:elem init in
    lower_indexed c ~addr ~elem ~esz rest (i + 1) k

and lower_fields c ~addr ~tag fields k = match fields with
  | [] -> k ()
  | (field, init) :: rest ->
    let fty = field_type c ~tag ~field in
    let store_field k =
      match Result.ok (Layout.bitfield_info c.e.layout ~tag ~field), init with
      | Some bf, Isingle e ->
        (* A bit-field initializer splices into the storage unit at `addr`. *)
        let@ v = E.lower_rval c.e e in
        E.bitfield_store c.e ~base:addr ~bf ~ty:fty ~value:v k
      | _ ->
        let*? off = Layout.offsetof c.e.layout ~tag ~field in
        let@ a = E.add_offset c.e addr off in
        lower_init c ~addr:a ~ty:fty init k in
    let@ () = store_field in
    lower_fields c ~addr ~tag rest k

let rec zero_region c ~addr ~size ~off k =
  if off >= size then k () else
    let w, (bty : IT.basic) =
      if size - off >= 8 then 8, `i64
      else if size - off >= 4 then 4, `i32
      else if size - off >= 2 then 2, `i16
      else 1, `i8 in
    let@ a = E.add_offset c.e addr off in
    let@ () = fun k ->
      let+ rest = k () in
      E.emit (`store ((bty :> IT.arg), E.zero_operand bty, a)) rest in
    zero_region c ~addr ~size ~off:(off + w) k

let rec needs_zero c (init : Texpr.init) ty = match init with
  | Isingle _ | Ioverlay _ -> false
  | Iunion {name; init} ->
    let tag = Lower_type.compound_tag_exn c.e.layout ty in
    needs_zero c init (field_type c ~tag ~field:name)
  | Iarray inits ->
    let elem = element_type c ty in
    let st = Layout.sizeof c.e.layout ty in
    let se = Layout.sizeof c.e.layout elem in
    let n = match st, se with
      | Ok asz, Ok esz when esz > 0 -> asz / esz
      | _ -> Int.max_value in
    List.length inits < n ||
    List.exists inits ~f:(fun i -> needs_zero c i elem)
  | Istruct fields ->
    let tag = Lower_type.compound_tag_exn c.e.layout ty in
    let count = match Type_env.find_tag (Layout.tenv c.e.layout) tag with
      | Some (Tcompound {fields; _}) -> List.length fields
      | _ -> Int.max_value in
    List.length fields < count ||
    List.exists fields ~f:(fun (f, i) ->
        needs_zero c i (field_type c ~tag ~field:f))

(* Bring a block-scoped local into scope. The local is in scope within
   its own initializer (§6.2.1). *)
let bind_localdecl c (ld : Tstmt.localdecl) =
  let* (name, slot), slotval = E.alloc_slot c.e.layout ld.name ld.ty in
  c.slots := slotval :: !(c.slots);
  let e = {c.e with slots = Smap.set c.e.slots ~key:name ~data:slot} in
  let c = {c with e} in
  let+ stmt = match ld.init with
    | None -> !!`nop
    | Some init ->
      let addr = `var slot in
      (* A partial aggregate initializer leaves the rest zero (§6.7.8);
         for a local, clear the slot first since omitted sub-objects are
         not stored. *)
      let@ () =
        if needs_zero c init ld.ty then fun k ->
          let*? size = Layout.sizeof c.e.layout ld.ty in
          zero_region c ~addr ~size ~off:0 k
        else fun k -> k () in
      let@ () = lower_init c ~addr ~ty:ld.ty init in
      !!`nop in
  c, stmt

(* {1 Instructions} *)

(* The result type of a call target (function or pointer-to-function). *)
let call_result c (fn : Texpr.t) = match E.norm c.e fn.ty with
  | Tfun {result; _} -> result
  | Tptr {pointee; _} ->
    begin match E.norm c.e pointee with
      | Tfun {result; _} -> result
      | _ -> failwith "lower: call of a non-function pointer"
    end
  | _ -> failwith "lower: call of a non-function"

(* If `fn` is a (pointer to a) variadic function, return the count of its
   fixed (non-variadic) parameters. *)
let variadic_fixed_count c (fn : Texpr.t) =
  let of_fun : Texpr.ty -> int option = function
    | Tfun {params = Some ps; variadic = true; _} -> Some (List.length ps)
    | _ -> None in
  match E.norm c.e fn.ty with
  | Tptr {pointee; _} -> of_fun (E.norm c.e pointee)
  | t -> of_fun t

let rec lower_instr c (instr : Tstmt.instr) k = match instr with
  | Icall {lval; fn; args} -> lower_call c ~lval ~fn ~args k
  | Iassign {lval; expr} ->
    store_into_lval c ~lval ~rhs:(E.lower_rval c.e expr) k
  | Ibuiltin {lval; name; args} -> lower_builtin c ~lval ~name ~args k

(* The `va_list` pointer operand of a variadic builtin: its first argument
   lowers to the address of the `va_list` object. *)
and lower_alist c (ap : Texpr.t) k =
  E.lower_rval c.e ap @@ function
  | `var x -> k (`var x : V.global)
  | `sym (s, o) -> k (`sym (s, o))
  | _ -> Ctx.failf "lower: va_list argument is not an lvalue" ()

and lower_builtin c ~lval ~name ~(args : Texpr.t list) k =
  match Builtins.find name, args, lval with
  | Some desc, [arg], Some lv ->
    let t = E.scalar_imm c.e desc.Builtins.operand in
    let rt = E.scalar_imm c.e lv.ty in
    let uop = match desc.Builtins.op with
      | Clz -> `clz t
      | Ctz -> `ctz t
      | Popcount -> `popcnt t
      | Bswap -> `bswap t in
    let@ v = E.lower_rval c.e arg in
    let* r = E.fresh_var in
    if IT.equal_imm t rt then
      let+ rest = store_result c ~lval:lv ~value:(`var r) k in
      E.emit (`uop (r, uop, v)) rest
    else
      let resize =
        if IT.sizeof_imm rt < IT.sizeof_imm t
        then `itrunc rt else `zext rt in
      let* r2 = E.fresh_var in
      let+ rest = store_result c ~lval:lv ~value:(`var r2) k in
      E.emit
        (`uop (r, uop, v))
        (E.emit
           (`uop (r2, resize, `var r))
           rest)
  | _ ->
    match name, args, lval with
    | "__builtin_va_start", [ap], None ->
      let@ g = lower_alist c ap in
      let+ rest = k () in
      E.emit (`vastart g) rest
    | "__builtin_va_end", [_ap], None ->
      (* XXX: for now, all of our supported targets treat `va_end` as
         a no-op. *)
      k ()
    | "__builtin_va_arg", [ap], Some lv ->
      let aty = Lower_type.arg_of c.e.layout lv.ty in
      let@ g = lower_alist c ap in
      let* r = E.fresh_var in
      let+ rest = store_result c ~lval:lv ~value:(`var r) k in
      E.emit (`vaarg (r, aty, g)) rest
    | _ -> Ctx.failf "lower: malformed builtin '%s'" name ()

and lower_call c ~lval ~(fn : Texpr.t) ~args k =
  (* Peel away the cast(s) that a function-to-pointer decay would
     have produced. *)
  let rec direct (e : Texpr.t) = match e.node with
    | Efun name -> Some name
    | Ecast {arg; _} -> direct arg
    | _ -> None in
  let dest k = match direct fn with
    | Some name -> k (`sym (name, 0) : V.global)
    | None -> E.lower_rval c.e fn @@ function
      | `var x -> k (`var x : V.global)
      | _ -> Ctx.failf "lower: unsupported indirect call target" () in
  (* Each argument materialized by value (whole structs loaded). *)
  let rec eval_args args k = match args with
    | [] -> k []
    | a :: rest ->
      let@ op = E.lower_rval c.e a in
      let@ v = as_value c a.ty op in
      let@ vs = eval_args rest in
      k (v :: vs) in
  let@ g = dest in
  let@ argv = eval_args args in
  (* Split off the variadic arguments (those past the fixed parameters). *)
  let fixed, vargs = match variadic_fixed_count c fn with
    | Some n -> List.split_n argv n
    | None -> argv, [] in
  match lval with
  | None ->
    (* Even though we're discarding the result, the IR requires us to
       bind it to a name. This will be optimized away later. *)
    let result = call_result c fn in
    let* bind = match Lower_type.ret_of c.e.layout result with
      | None -> !!None
      | Some ret ->
        let+ r = E.fresh_var in
        Some (r, ret) in
    let+ rest = k () in
    E.emit (`call (bind, g, fixed, vargs, false)) rest
  | Some lv ->
    let result = call_result c fn in
    let ret = match Lower_type.ret_of c.e.layout result with
      | None -> failwith "lower: assigning a void call result"
      | Some r -> r in
    let* r = E.fresh_var in
    let+ rest = store_result c ~lval:lv ~value:(`var r) k in
    let call = `call (Some (r, ret), g, fixed, vargs, false) in
    E.emit call rest

(* {1 Switch flattening} *)

type sw_label = [`case of Bv.t | `default]
type sw_body = [`stmt of Tstmt.t | `decl of Tstmt.localdecl]
type sw_event = [sw_label | sw_body]

let rec flatten_sw (s : Tstmt.t) acc = match s with
  | Sblock items -> List.fold_right items ~init:acc ~f:flatten_sw_item
  | Scase {value; body} -> `case value :: flatten_sw body acc
  | Sdefault body -> `default :: flatten_sw body acc
  | s -> `stmt s :: acc

and flatten_sw_item (item : Tstmt.blkitem) acc = match item with
  | Bstmt s -> flatten_sw s acc
  | Bdecl ld -> `decl ld :: acc

(* Group flattened events into (label, body) pairs in source order.
   Statements before the first label are unreachable in standard C and
   are dropped. *)
let group_cases (evs : sw_event list) =
  let finish label body acc = match label with
    | None -> acc
    | Some l -> (l, List.rev body) :: acc in
  let rec go label body acc = function
    | [] -> List.rev (finish label body acc)
    | (`case _ | `default as l) :: rest ->
      go (Some l) [] (finish label body acc) rest
    | (`stmt _ | `decl _ as it) :: rest -> go label (it :: body) acc rest in
  go None [] [] evs

(* Does the switch body contain a `case`/`default` label that the structured
   path (`flatten_sw`) cannot see? For example, we could have a body nested
   inside a control-flow statement rather than directly in the switch body's
   block structure. Such a switch (the archetype being Duff's Device) must be
   lowered the general way.

   `flatten_sw` descends only `Sblock`, `Scase`, and`Sdefault`. A case reached
   only by first entering an `Sif`, loop, or `Slabel` is invisible to it. A
   nested `Sswitch` owns its own labels, so we do not look inside one.
*)
let rec has_nested_case ?(top = true) (s : Tstmt.t) = match s with
  | (Scase _ | Sdefault _) when not top -> true
  | Scase {body; _} | Sdefault body -> has_nested_case ~top body
  | Sblock items ->
    List.exists items ~f:(function
        | Tstmt.Bstmt s -> has_nested_case ~top s
        | Tstmt.Bdecl _ -> false)
  | Sswitch _ -> false
  | Sif {then_; else_; _} ->
    has_nested_case ~top:false then_
    || Option.exists else_ ~f:(has_nested_case ~top:false)
  | Swhile {body; _} | Sdowhile {body; _}
  | Sfor {body; _} | Slabel {body; _} -> has_nested_case ~top:false body
  | Sinstr _ | Sgoto _ | Sgotoind _ | Sbreak | Scontinue | Sreturn _ -> false

(* Collect every `case` value and whether a `default` exists in this switch,
   descending into all nested statements except a nested `Sswitch` (whose
   labels belong to it).

   Values are returned in source order.
*)
let collect_cases (s : Tstmt.t) =
  let rec go (s : Tstmt.t) ((vals, dflt) as acc) = match s with
    | Scase {value; body} -> go body (value :: vals, dflt)
    | Sdefault body -> go body (vals, true)
    | Sblock items ->
      List.fold items ~init:acc ~f:(fun acc -> function
          | Tstmt.Bstmt s -> go s acc
          | Tstmt.Bdecl _ -> acc)
    | Sif {then_; else_; _} ->
      let acc = go then_ acc in
      Option.fold else_ ~init:acc ~f:(fun acc s -> go s acc)
    | Swhile {body; _} | Sdowhile {body; _}
    | Sfor {body; _} | Slabel {body; _} -> go body acc
    | Sswitch _
    | Sinstr _ | Sgoto _ | Sgotoind _ | Sbreak | Scontinue | Sreturn _ -> acc in
  let vals, dflt = go s ([], false) in
  List.rev vals, dflt

(* {1 Statements} *)

let rec lower_stmt c (s : Tstmt.t) = match s with
  | Sblock items -> lower_block c items
  | Sinstr instrs -> lower_instrs c instrs
  | Sif {cond; then_; else_} -> lower_if c cond then_ else_
  | Swhile {cond; body} -> lower_while c cond body
  | Sdowhile {body; cond} -> lower_dowhile c body cond
  | Sfor {init; cond; step; body} -> lower_for c init cond step body
  | Sreturn None -> !!(`ret None)
  | Sreturn Some e ->
    let@ v = E.lower_rval c.e e in
    let@ rv = as_value c e.ty v in
    !!(`ret (Some rv))
  | Sbreak ->
    begin match c.brk with
      | `structured -> !!`break
      | `goto l -> !!(`goto (`label l))
    end
  | Scontinue -> !!`continue
  | Sgoto name ->
    !!(`goto (`label (Smap.find_exn c.labels name)))
  (* GNU computed `goto *e`: `e` is an integer index into the function's
     address-taken labels (produced by `&&label`).

     Dispatch it through a jump-table `sw` with one arm per label, in the
     same index order the elaborator assigned.

     An out-of-range index is undefined behavior, so the default arm traps.
  *)
  | Sgotoind e ->
    let b = scalar_basic c e.ty in
    let ty = E.scalar_imm c.e e.ty in
    let@ v = E.lower_rval c.e e in
    let@ idx = as_index b v in
    let m = Bv.modulus (Cgen.Type.sizeof_imm ty) in
    let mki i = Bv.(int i mod m) in
    let cases =
      List.mapi c.labaddrs ~f:(fun i name ->
          let l = Smap.find_exn c.labels name in
          `case (mki i, `goto (`label l)))
      @ [`default `hlt] in
    !!(`sw (idx, ty, cases))
  | Slabel {name; body} ->
    let+ bs = lower_stmt c body in
    let l = Smap.find_exn c.labels name in
    `label (l, bs)
  | Sswitch {expr; body} -> lower_switch c ~expr ~body
  (* A `case`/`default` reached here (rather than being collected by the
     structured-switch path) is a label buried inside the switch body.

     The general Duff-style lowering has recorded a target label for it,
     which we mark here and then continue lowering the statement with the
     associated label. The dispatch built by `lower_switch_general` jumps
     to these labels.
  *)
  | Scase {value; body} ->
    begin match List.Assoc.find c.case_labels value ~equal:Bv.equal with
      | None -> Ctx.failf "lower: `case` label outside of a switch" ()
      | Some l ->
        let+ bs = lower_stmt c body in
        `label (l, bs)
    end
  | Sdefault body ->
    begin match c.default_label with
      | None -> Ctx.failf "lower: `default` label outside of a switch" ()
      | Some l ->
        let+ bs = lower_stmt c body in
        `label (l, bs)
    end

and lower_if c cond then_ else_ =
  let@ v = E.lower_rval c.e cond in
  let* ts = lower_stmt c then_ in
  let+ es = match else_ with
    | Some s -> lower_stmt c s
    | None -> !!`nop in
  `ite (cond_nonzero c cond.ty v, ts, es)

and lower_while c cond body =
  (* Any `break` is structured according to the loop, not an enclosing
     `switch`. *)
  let* bs = lower_stmt {c with brk = `structured} body in
  let+ test = E.lower_rval c.e cond @@ fun v ->
    !!(`ite (cond_nonzero c cond.ty v, `nop, `break)) in
  (* The condition is tested at the top of the body; a `continue` lands
     on the empty step region and falls back through to the test. *)
  `loop (S.Stmt.seq [test; bs], `nop)

and lower_dowhile c body cond =
  let* bs = lower_stmt {c with brk = `structured} body in
  let+ test = E.lower_rval c.e cond @@ fun v ->
    !!(`ite (cond_nonzero c cond.ty v, `nop, `break)) in
  (* The step region is the trailing condition test, which is exactly
     where a `continue` should land. *)
  `loop (bs, test)

and lower_for c init cond step body =
  (* A declaration in the for-init is scoped to the whole statement (§6.8.5.3),
     so thread the extended context through cond, step, and body. *)
  let* c, init_s = lower_forinit c init in
  let* bs = lower_stmt {c with brk = `structured} body in
  let* step_s = lower_instrs c step in
  let+ test = match cond with
    | None -> !!`nop
    | Some cnd ->
      let@ v = E.lower_rval c.e cnd in
      !!(`ite (cond_nonzero c cnd.ty v, `nop, `break)) in
  (* The increment is the step region, where a `continue` lands; it falls
     back through to the test at the top of the body. *)
  S.Stmt.seq [
    init_s;
    `loop (S.Stmt.seq [test; bs], step_s);
  ]

and lower_forinit c (fi : Tstmt.forinit option) = match fi with
  | Some FIexpr instrs -> let+ s = lower_instrs c instrs in c, s
  | Some FIdecl ld -> bind_localdecl c ld
  | None -> !!(c, `nop)

and lower_switch c ~(expr : Texpr.t) ~body =
  if has_nested_case body
  then lower_switch_general c ~expr ~body
  else lower_switch_structured c ~expr ~body

(* The common case: every `case`/`default` sits directly in the switch body. *)
and lower_switch_structured c ~(expr : Texpr.t) ~body =
  let c = {c with brk = `structured} in
  let groups = group_cases (flatten_sw body []) in
  let rec build = function
    | [] -> !![]
    | (label, items) :: rest ->
      let* b = lower_case_items c items in
      let+ cs = build rest in
      let case = match label with
        | `case v -> `case (v, b)
        | `default -> `default b in
      case :: cs in
  let b = scalar_basic c expr.ty in
  let@ v = E.lower_rval c.e expr in
  let@ idx = as_index b v in
  let+ cases = build groups in
  let ty = E.scalar_imm c.e expr.ty in
  `sw (idx, ty, cases)

(* The general case (Duff's device et al.): a `case`/`default` label is buried
   inside the switch body's control flow, so the switch cannot be a single
   self-contained structured switch. Instead we:

   - Give every `case` value, the `default`, and the switch's end a fresh
     label.
   - Lower the whole body once, in place, turning each `Scase`/`Sdefault` into
     a "label" marker (see `lower_stmt`) and each switch-targeting `break` into
     a `goto` to the end label (via `brk`).
   - Prepend a jump-table `sw` whose arms `goto` the case labels and whose
     `default` `goto`s the `default` label (or the end, if none).
*)
and lower_switch_general c ~(expr : Texpr.t) ~body =
  let values, has_default = collect_cases body in
  let* case_labels =
    Ctx.List.map values ~f:(fun v ->
        let+ l = Ctx.Label.fresh in
        v, l) in
  let* default_label =
    if has_default then
      let+ l = Ctx.Label.fresh in
      Some l
    else !!None in
  let* l_end = Ctx.Label.fresh in
  let dispatch_cases =
    List.map case_labels ~f:(fun (v, l) -> `case (v, `goto (`label l)))
    @ [`default (`goto (`label (Option.value default_label ~default:l_end)))] in
  let cbody = {c with brk = `goto l_end; case_labels; default_label} in
  let b = scalar_basic c expr.ty in
  let ty = E.scalar_imm c.e expr.ty in
  let@ v = E.lower_rval c.e expr in
  let@ idx = as_index b v in
  let+ body_s = lower_stmt cbody body in
  S.Stmt.seq [
    `sw (idx, ty, dispatch_cases);
    body_s;
    `label (l_end, `nop);
  ]

and lower_case_items c items = match items with
  | [] -> !!`nop
  | `stmt s :: rest ->
    let* a = lower_stmt c s in
    let+ b = lower_case_items c rest in
    S.Stmt.seq [a; b]
  | `decl ld :: rest ->
    let* c, a = bind_localdecl c ld in
    let+ b = lower_case_items c rest in
    S.Stmt.seq [a; b]

and lower_block c items =
  (* Thread the context so a declaration is in scope only for the statements
     that follow it in the block, restoring the outer scope on exit. *)
  let rec go c = function
    | [] -> !!`nop
    | Tstmt.Bstmt s :: rest ->
      let* a = lower_stmt c s in
      let+ b = go c rest in
      S.Stmt.seq [a; b]
    | Tstmt.Bdecl ld :: rest ->
      let* c, a = bind_localdecl c ld in
      let+ b = go c rest in
      S.Stmt.seq [a; b] in
  go c items

and lower_instrs c instrs =
  let rec go = function
    | [] -> !!`nop
    | i :: rest ->
      let@ () = lower_instr c i in
      go rest in
  go instrs
