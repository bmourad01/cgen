(* Initializer flattening (C99 §6.7.8).

   Turns an untyped, designator-based `Expr.init` into the positional
   typed `Texpr.init`, resolving:

   - scalar initializers (with or without surrounding braces);
   - string-literal initialization of character arrays;
   - aggregate brace lists, with positional fill, `.field`/`[index]`
     designators, and brace elision (a bare value descends into an
     aggregate sub-object and consumes as many following items as that
     sub-object needs);
   - zero-fill of omitted elements/members;
   - determination of an unspecified top-level array bound.

   Because designated initializers can be nested and/or out-of-order,
   we need to carry some state of the current subobject we're building.
   Interestingly, this takes the form of something similar to a pushdown
   automaton (PDA).
*)

open Core
open Regular.Std

module Bv = Cgen.Bv
module EC = Elab_conv
module ET = Elab_type
module TE = Type_env
module Ftree = Cgen_containers.Ftree

open Elab_common

(* The ordered (name, type) members of a struct/union tag.

   Unnamed bit-fields (including zero-width ones) take no initializer
   and are skipped during positional initialization (§6.7.8).
*)
let tag_fields tenv name =
  let unnamed_bitfield f =
    Option.is_some f.Tdecl.fbits && String.is_empty f.Tdecl.fname in
  match TE.find_tag tenv name with
  | Some (Tcompound {fields; _}) ->
    List.filter fields ~f:(Fn.non unnamed_bitfield) |>
    Array.of_list_map ~f:(fun f -> f.Tdecl.fname, f.Tdecl.fty) |>
    Option.some
  | _ -> None

(* A compact zero initializer for a (sub)object of type `ty`,
   relying on the short-list convention for aggregates. *)
let rec zero_init tenv ty : Texpr.init =
  match ET.normalize tenv ty with
  | Tarray _ -> Iarray []
  | Tnamed {kind = `struct_; _} -> Istruct []
  | Tnamed {kind = `union; name; _} ->
    begin match tag_fields tenv name with
      | Some [||] | None -> Istruct []
      | Some fs ->
        let fname, fty = fs.(0) in
        Iunion {name = fname; init = zero_init tenv fty}
    end
  | _ -> Isingle (scalar_zero ty)

let is_char_ty tenv ty = match ET.normalize tenv ty with
  | Tbase {base = Bchar | Bint Ichar _; _} -> true
  | _ -> false

let is_char_array_ty tenv ty = match ET.normalize tenv ty with
  | Tarray {elem; _} -> is_char_ty tenv elem
  | _ -> false

let string_init_of (i : _ Expr.init) = match i with
  | Isingle e | Icompound [[], Isingle e] -> string_of_expr_opt e
  | _ -> None

(* A description of an aggregate's sub-objects, used by the walk. *)
type agg =
  | Astruct of (string * Texpr.ty) array
  | Aunion of (string * Texpr.ty) array
  | Aarray of {
      elem : Texpr.ty;
      size : int option;
    }

let agg_elem_ty agg i = match agg with
  | Aarray {elem; _} -> elem
  | Astruct fs | Aunion fs -> snd fs.(i)

(* The number of sub-objects, or `None` for an unspecified-length
   array. A union is initialized one member at a time. *)
let agg_count = function
  | Aarray {size; _} -> size
  | Astruct fs -> Some (Array.length fs)
  | Aunion _ -> Some 1

let fold_maxi xs = Ftree.fold xs ~init:(-1) ~f:(fun m (i, _) -> Int.max m i)

(* The output "tape" of the initializer automaton: a deferred,
   partially-built initializer.

   Either a leaf (a scalar value, a string, or an opaque whole-aggregate
   value) or an aggregate whose explicitly-initialized children are
   recorded as (index, sub) in source order. for an overlay, we refine
   via later member designators.

   Materialization is deferred so contributions to the same index merge:
   C99 designators are absolute from the root, so `.s.a = 1, .s.b = 2`
   both target `s` and accumulate.
*)
type sub =
  | Sleaf of Texpr.init
  | Sagg of agg * (int * sub) Ftree.t
  | Soverlay of Texpr.init * agg * (int * sub) Ftree.t

(* Combine two contributions to the same sub-object, from oldest to
   newest.

   Aggregates merge their children, which are resolved recursively when
   materialized. A later whole value overrides; a prior whole value
   refined by member designators becomes an overlay.
*)
let merge_sub a b = match a, b with
  | Sagg (agg, c1), Sagg (_, c2) ->
    Sagg (agg, Ftree.append c1 c2)
  | Sleaf base, Sagg (agg, c) ->
    Soverlay (base, agg, c)
  | Soverlay (base, agg, c1), Sagg (_, c2) ->
    Soverlay (base, agg, Ftree.append c1 c2)
  | _, _ -> b

let sub_at xs i =
  Ftree.enum xs |> Seq.filter_map ~f:(fun (j, s) ->
      Option.some_if (j = i) s) |> Seq.next |> function
  | Some (x, xs) -> Some (Seq.fold xs ~init:x ~f:merge_sub)
  | None -> None

(* Materialize the deferred tree into a positional `Texpr.init`, merging
   same-index contributions and filling interior gaps with compact zero
   inits (trailing gaps rely on the short-list convention). *)
let rec mat_sub tenv = function
  | Sleaf init -> init
  | Sagg (agg, assigns) -> mat_agg tenv agg assigns
  | Soverlay (base, agg, overrides) ->
    let base = match base with
      | Isingle e -> e
      | _ -> failwith "elab_init: overlay base is not a value" in
    Ioverlay {base; over = mat_overrides tenv agg overrides}

and mat_overrides tenv agg overrides : Texpr.init =
  let sub_at = sub_at overrides in
  match agg with
  | Astruct fs ->
    let inits =
      Ftree.enum overrides |>
      Seq.map ~f:fst |>
      Seq.to_list |>
      List.dedup_and_sort ~compare:Int.compare |>
      List.map ~f:(fun i ->
          let f = fst fs.(i) in
          let init = mat_sub tenv (Option.value_exn @@ sub_at i) in
          f, init) in
    Istruct inits
  | Aunion fs ->
    begin match Ftree.last overrides with
      | None -> Istruct []
      | Some (i, _) ->
        Iunion {
          name = fst fs.(i);
          init = mat_sub tenv (Option.value_exn (sub_at i));
        }
    end
  | Aarray _ -> assert false (* C has no whole-array rvalues to overlay *)

and mat_agg tenv agg assigns : Texpr.init =
  let maxi = fold_maxi assigns in
  let sub_at = sub_at assigns in
  match agg with
  | Aunion _ ->
    begin match Ftree.last assigns with
      | None -> Istruct []
      | Some (idx, _) ->
        let name = match agg with
          | Aunion fs -> fst fs.(idx)
          | _ -> assert false in
        Iunion {name; init = mat_sub tenv (Option.value_exn (sub_at idx))}
    end
  | Astruct fs ->
    let inits =
      List.init (maxi + 1) ~f:(fun i ->
          let name, fty = fs.(i) in
          let init = match sub_at i with
            | Some s -> mat_sub tenv s
            | None -> zero_init tenv fty in
          name, init) in
    Istruct inits
  | Aarray {elem; _} ->
    let inits =
      List.init (maxi + 1) ~f:(fun i ->
          match sub_at i with
          | Some s -> mat_sub tenv s
          | None -> zero_init tenv elem) in
    Iarray inits

module Make(A : Annotation) = struct
  module Ctx = Elab_ctx.Make(A)
  open Ctx
  open Syntax

  let classify_aggregate ty =
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    match ET.normalize tenv ty with
    | Tarray {elem; size = None; _} -> !!(Some (Aarray {elem; size = None}))
    | Tarray {elem; size = Some e; _} ->
      let+? n = Eval.int_const (Eval.create_init layout) e in
      Some (Aarray {elem; size = Some (Bv.to_int n)})
    | Tnamed {kind = `struct_; name; _} ->
      begin match tag_fields tenv name with
        | Some fs -> !!(Some (Astruct fs))
        | None -> !!None
      end
    | Tnamed {kind = `union; name; _} ->
      begin match tag_fields tenv name with
        | Some fs -> !!(Some (Aunion fs))
        | None -> !!None
      end
    | _ -> !!None

  (* A character array initialized by a string literal.

     Returns the completed array type (its bound determined when
     unspecified) and the init.

     Independent of the leaf-elaboration state.
  *)
  let string_array_init target s =
    let* layout = M.gets Ctx.layout in
    let dm = Layout.dmodel layout in
    let bits = Data_model.pointer_bits dm in
    let size_t = Data_model.size_t dm in
    let module B = (val Bv.modular bits) in
    let tenv = Layout.tenv layout in
    let len = String.length s in
    let+ size = match ET.normalize tenv target with
      | Tarray {size = None; _} -> !!(len + 1)
      | Tarray {size = Some e; _} ->
        let* n = Eval.int_const (Eval.create_init layout) e >|? Bv.to_int in
        if n >= len then !!n else
          Ctx.fatal "string literal too long for '%a'" pp_ty target ()
      | _ ->
        Ctx.fatal "string initializer for non-array type '%a'" pp_ty target () in
    let szexpr = Texpr.int_ (B.int size) ~ty:size_t in
    let elem = Type.plain_char_ () in
    let arr_ty = Type.array ~size:szexpr elem in
    let size = Texpr.int_ (B.int (len + 1)) ~ty:size_t in
    let str_ty = Type.array ~size elem in
    arr_ty, Texpr.Isingle (Texpr.str s ~ty:str_ty)

  type env = {
    elab_rval : A.ann Expr.t -> (Texpr.t -> Tstmt.t M.m) -> Tstmt.t M.m;
    mutable prefix : Tstmt.t list; (* accumulated in reverse *)
    require_const : bool; (* enforce the constant-expression rule where needed *)
  }

  (* Elaborate `e`, queueing its side effects; return its rvalue. *)
  let capture env e =
    let slot = ref None in
    let+ stmt = env.elab_rval e @@ fun rv ->
      slot := Some rv;
      !!(Tstmt.Sinstr []) in
    env.prefix <- stmt :: env.prefix;
    Option.value_exn !slot

  (* The type `e` would have, with no side effects committed.

     This is used to decide whether a bare value initializes a whole
     aggregate sub-object or starts filling it by brace elision.
  *)
  let type_of_dry env e =
    let@ () = Ctx.discarding_temps in
    let slot = ref None in
    let+ _ = env.elab_rval e @@ fun rv ->
      slot := Some rv;
      !!(Tstmt.Sinstr []) in
    (Option.value_exn !slot).Texpr.ty

  (* C99 §6.7.8 ¶4: every expression in an initializer for an object
     with static storage duration must be a constant expression.

     When that is required, fold `rv` (which surfaces the constraint
     violations the standard treats as ill-formed in a constant context,
     e.g. overflow or division by zero) and require the result to reduce
     to an actual constant: an arithmetic or address constant, a string,
     or null.

     The expression itself is left unchanged for lowering to re-fold.
  *)
  let enforce_const env rv =
    if env.require_const then
      let* layout = M.gets Ctx.layout in
      let eval = Eval.create_init layout in
      let*? folded = Eval.fold eval rv in
      match Eval.const eval folded with
      | Error _ -> Ctx.fatal "initializer element is not a constant expression" ()
      | Ok _ -> !!rv
    else !!rv

  (* A scalar leaf, converted to its target type. *)
  let scalar_leaf env target e =
    let* rv = capture env e in
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    let eval = Eval.create_init layout in
    let*? rv, w = EC.convert_for_assign tenv eval ~lhs:target ~rhs:rv in
    let* () = Ctx.warn_opt w in
    enforce_const env rv

  (* Resolve a single designator against the current aggregate to a
     sub-object index. *)
  let resolve_designator env agg (d : A.ann Expr.designator) =
    match d, agg with
    | Dfield name, (Astruct fs | Aunion fs) ->
      begin match Array.findi fs ~f:(fun _ (n, _) -> String.(n = name)) with
        | Some (i, _) -> !!i
        | None -> Ctx.fatal "no member '%s' in aggregate" name ()
      end
    | Dfield name, Aarray _ ->
      Ctx.fatal "field designator '.%s' for an array type" name ()
    | Dindex e, Aarray _ ->
      let* rv = capture env e in
      let* layout = M.gets Ctx.layout in
      let+? n = Eval.int_const (Eval.create_init layout) rv in
      Bv.to_int n
    | Dindex _, (Astruct _ | Aunion _) ->
      Ctx.fatal "array designator '[...]' for a struct/union type" ()

  (* The initializer automaton (C99 §6.7.8)

     `consume` fills one aggregate "barrier" (the object named by an
     enclosing `{...}`). It walks the items maintaining a cursor stack
     whose last frame is the barrier base and whose upper frames are
     the `Descent` frames reached by brace elision or a designator
     chain.

     Transitions:
     - a positional value is placed and the cursor advances, popping
       exhausted descents
     - a bare scalar whose target is an aggregate elides into it (push)
     - a designator resets to the barrier and navigates from there, so
       `.s.a, .s.b` merge into `s`
     - a `{...}` value recurses as a new barrier

     Children are recorded deferred and merged/zero-filled by `mat_agg`.
  *)

  (* Place a brace-enclosed init `{items}` into `sty`, deferred. *)
  let rec braced_sub env sty items =
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    match string_init_of (Icompound items) with
    | Some s when is_char_array_ty tenv sty ->
      let+ i = string_array_init sty s >>| snd in Sleaf i
    | _ ->
      if EC.is_scalar tenv sty then
        (* A braced scalar: `{e}`, `{{e}}`, or `{}`. *)
        match items with
        | [] -> !!(Sleaf (zero_init tenv sty))
        | [[], inner] -> value_sub env sty inner
        | _ -> Ctx.fatal "too many initializers for scalar type '%a'" pp_ty sty ()
      else
        classify_aggregate sty >>= function
        | None -> Ctx.fatal "cannot brace-initialize type '%a'" pp_ty sty ()
        | Some agg ->
          let+ assigns = consume env agg items in
          Sagg (agg, assigns)

  (* Place a whole init (a value or a brace) into `sty`, deferred.

     Brace elision is the automaton's job. By the time this runs on a
     scalar target the cursor has already descended.
  *)
  and value_sub env sty (i : A.ann Expr.init) = match i with
    | Icompound items -> braced_sub env sty items
    (* A compound-literal initializer `(T){...}` for an aggregate target is
       decomposed to its brace, so it merges field-wise with later designators
       (and emits as constant data when static) rather than being an opaque
       value. For a scalar target it is an ordinary expression. *)
    | Isingle ({node = Ecompound {init; _}; _} as e) ->
      let* layout = M.gets Ctx.layout in
      let tenv = Layout.tenv layout in
      if EC.is_scalar tenv sty then
        let@ () = Ctx.with_location_of e.ann in
        let+ rv = scalar_leaf env sty e in
        Sleaf (Isingle rv)
      else value_sub env sty init
    | Isingle e ->
      let@ () = Ctx.with_location_of e.ann in
      let* layout = M.gets Ctx.layout in
      let tenv = Layout.tenv layout in
      if EC.is_scalar tenv sty then
        let+ rv = scalar_leaf env sty e in
        Sleaf (Isingle rv)
      else if is_string_expr e && is_char_array_ty tenv sty then
        let+ i = string_array_init sty (string_of_expr e) >>| snd in
        Sleaf i
      else
        let* ety = type_of_dry env e in
        let eval = Eval.create_init layout in
        if EC.compatible tenv eval sty ety then
          let* rv = capture env e in
          let+ rv = enforce_const env rv in
          Sleaf (Isingle rv)
        else
          Ctx.fatal "invalid initializer of type '%a' for '%a'" pp_ty ety pp_ty sty ()

  (* Decide between placing `init` at a focus of type `sty` and eliding a
     bare scalar into the aggregate `sty` (which the caller descends). *)
  and place_or_elide env sty (i : A.ann Expr.init) = match i with
    | Icompound _ | Isingle {node = Ecompound _; _} ->
      let+ s = value_sub env sty i in `Place s
    | Isingle e ->
      let* layout = M.gets Ctx.layout in
      let tenv = Layout.tenv layout in
      if EC.is_scalar tenv sty
      || (is_string_expr e && is_char_array_ty tenv sty)
      then
        let+ s = value_sub env sty i in
        `Place s
      else
        let* ety = type_of_dry env e in
        let eval = Eval.create_init layout in
        if EC.compatible tenv eval sty ety then
          let+ s = value_sub env sty i in
          `Place s
        else
          (* A bare scalar into an aggregate elides if we can descend. *)
          classify_aggregate sty >>= function
          | Some _ -> !!`Elide
          | None ->
            let@ () = Ctx.with_location_of e.ann in
            Ctx.fatal "invalid initializer of type '%a' for '%a'"
              pp_ty ety pp_ty sty ()

  (* Resolve a whole designator chain from the barrier aggregate,
     returning the cursor stack.

     The reset-to-barrier (C99's "current object" returns to the nearest
     enclosing brace) is implicit, so we always navigate from `barrier`.
  *)
  and navigate env barrier chain =
    let rec go agg = function
      | [] -> assert false (* Designator chains are non-empty *)
      | [d] ->
        let+ i = resolve_designator env agg d in
        Ftree.singleton (agg, i)
      | d :: ds ->
        let* i = resolve_designator env agg d in
        classify_aggregate (agg_elem_ty agg i) >>= function
        | None -> Ctx.fatal "designator descends into a non-aggregate type" ()
        | Some sub_agg ->
          let+ deeper = go sub_agg ds in
          Ftree.snoc deeper (agg, i) in
    go barrier chain

  (* Fill the aggregate `barrier`; returns its deferred children. *)
  and consume env barrier items : (int * sub) Ftree.t M.m =
    (* Advance the cursor: bump the index of the top (head) frame. *)
    let bump stack = Ftree.update stack 0 ~f:(fun (a, i) -> a, i + 1) in
    let full (a, i) = match agg_count a with
      | Some n -> i >= n
      | None -> false in
    (* Pop descents that the cursor has run off the end of . *)
    let rec settle stack =
      if full (Ftree.head_exn stack) then
        let below = Ftree.tail_exn stack in
        if Ftree.is_empty below
        then None (* Barrier itself is full *)
        else settle (bump below)
      else Some stack in
    let place stack sub acc =
      let descents, (_, base) = Ftree.rear_exn stack in
      let nested =
        Ftree.fold_left descents ~init:sub
          ~f:(fun s (a, i) -> Sagg (a, Ftree.singleton (i, s))) in
      Ftree.snoc acc (base, nested) in
    let rec step stack acc init rest =
      let fagg, fidx = Ftree.head_exn stack in
      place_or_elide env (agg_elem_ty fagg fidx) init >>= function
      | `Place sub -> go (bump stack) (place stack sub acc) rest
      | `Elide ->
        (* Push and re-place the now-positional value *)
        classify_aggregate (agg_elem_ty fagg fidx) >>= function
        | None -> assert false
        | Some sub_agg ->
          let stack = Ftree.cons stack (sub_agg, 0) in
          let work = ([], init) :: rest in
          go stack acc work
    and go stack acc = function
      | [] -> !!acc
      | ([], init) :: rest ->
        (* Positional, so we advance past exhausted descents first *)
        begin match settle stack with
          | Some stack -> step stack acc init rest
          | None -> Ctx.fatal "excess elements in initializer" ()
        end
      | (desigs, init) :: rest ->
        (* Designated, so we reset to barrier and navigate *)
        let* stack = navigate env barrier desigs in
        step stack acc init rest in
    let stack = Ftree.singleton (barrier, 0) in
    go stack Ftree.empty items

  (* Top-level orchestration:

     - handle string init
     - handle an unspecified top-level array bound
     - otherwise, place the init into `ty`.
  *)
  let top env ty i =
    let* layout = M.gets Ctx.layout in
    let tenv = Layout.tenv layout in
    match string_init_of i with
    | Some s when is_char_array_ty tenv ty ->
      string_array_init ty s
    | _ ->
      match ET.normalize tenv ty with
      | Tarray {elem; size = None; _} ->
        let dm = Layout.dmodel layout in
        let size_t = Data_model.size_t dm in
        let bits = Data_model.pointer_bits dm in
        let module B = (val Bv.modular bits) in
        (* Unspecified bound: determined by the initializer. *)
        let items = match i with
          | Icompound items -> items
          | Isingle _ -> [[], i] in
        let agg = Aarray {elem; size = None} in
        let+ assigns = consume env agg items in
        let maxi = fold_maxi assigns in
        let szexpr = Texpr.int_ (B.int (maxi + 1)) ~ty:size_t in
        let ty = Type.array ~size:szexpr elem in
        let init = mat_sub tenv @@ Sagg (agg, assigns) in
        ty, init
      | _ ->
        let+ init = value_sub env ty i >>| mat_sub tenv in
        ty, init

  (* Public entry.

     Returns:
     - the side-effect prefix
     - the (possibly completed) object type
     - the flattened initializer.
  *)
  let elab ?(require_const = false) ~elab_rval ~ty i =
    let env = {elab_rval; prefix = []; require_const} in
    let+ completed_ty, init = top env ty i in
    let pre = mkblock @@ List.rev_map env.prefix ~f:Tstmt.bstmt in
    pre, completed_ty, init
end
