(* Declaration elaboration (C99 §6.7, §6.9): `'a Decl.t` to `Tdecl.t`.

   Constant contexts at file scope (array sizes, enum values, bit-field
   widths, and object initializers) are evaluated under a scratch
   function context so the expression elaborator's temporary allocator
   never trips on input that isn't actually a constant; a non-constant
   operand then fails the constant fold with a diagnostic rather than
   crashing.

   The driver in `elab.ml` threads the elaborator state across the unit
   and assembles the final `Tcunit.t`.
*)

open Core
open Elab_common

module Bv = Cgen_utils.Bv
module Ftree = Cgen_containers.Ftree
module EC = Elab_conv
module TE = Type_env

(* §6.7.5.3 ¶7-8: a parameter of array type is adjusted to a pointer to
   the element type, and a parameter of function type to a pointer to the
   function. The type is normalized first, so an array/function reached
   through a typedef (notably a `va_list` parameter) is adjusted too. *)
let param_decay tenv (ty : Texpr.ty) : Texpr.ty =
  match Elab_type.normalize tenv ty with
  | Tarray {elem; cv; restrict; _} ->
    (* §6.7.6.3 ¶7: the bracket type qualifiers of an array parameter qualify
       the pointer it decays to. The `static` size assertion has no home on the
       pointer type, so it is dropped here. *)
    Type.ptr ~cv ~restrict elem
  | Tfun _ -> Type.ptr ty
  | _ -> ty

let linkage_of : Stmt.storagecls -> Tdecl.linkage = function
  | SCstatic -> Lstatic
  | _ -> Lextern

(* Hoist a function's collected temporaries to the top of its body as
   block-local declarations.

   `tmps` is in most-recently-allocated-first order, so reverse it back
   to allocation order.
*)
let prepend_tmps tmps (body : Tstmt.t) = match tmps with
  | [] -> body
  | _ ->
    let decls = List.rev_map tmps ~f:Tstmt.bdecl in
    match body with
    | Sblock items -> Tstmt.block (decls @ items)
    | s -> Tstmt.block (decls @ [Tstmt.bstmt s])

(* Collect a function body's defined labels and `goto` targets, for the
   whole-function label checks (§6.8.1, §6.8.6.1). *)
let rec collect_labels ((defined, used) as acc) (s : Tstmt.t) = match s with
  | Slabel {name; body} ->
    collect_labels (name :: defined, used) body
  | Sgoto name -> defined, name :: used
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
  | Sdefault body -> collect_labels acc body
  | Sgotoind _ | Sbreak | Scontinue | Sreturn _ | Sinstr _ -> acc

module Make(A : Annotation) = struct
  module S = Elab_stmt.Make(A)
  module E = Elab_expr.Make(A)
  module Ctx = S.Ctx
  module ET = S.ET
  module EI = S.EI

  open Ctx
  open M.Syntax

  (* Run `f` with a fresh, throwaway function context installed, so the
     temporary allocator is available even at file scope.

     The prior context is restored afterwards.
  *)
  let with_scratch_fnctx f =
    let* saved = M.gets fnctx in
    let* () =
      M.update @@ fun c ->
      {c with fnctx = Some (Elab_ctx.create_fnctx ~retty:(Type.void ()) ())} in
    let* x = f () in
    let+ () = M.update @@ fun c -> {c with fnctx = saved} in
    x

  (* Elaborate `e` as a file-scope integer constant expression. *)
  let eval_const_int (e : A.ann Expr.t) : Bv.t M.m =
    let@ () = with_scratch_fnctx in
    let slot = ref None in
    let* _ = E.elab_rval e @@ fun rv ->
      slot := Some rv;
      !!(Tstmt.Sinstr []) in
    let rv = Option.value_exn !slot in
    let* layout = M.gets Ctx.layout in
    Ctx.lift_err @@ Eval.int_const (Eval.create_init layout) rv

  (* Array-size callback for `ET.elab`: fold to a constant `int` literal.

     File-scope arrays must have constant size (no VLAs).
  *)
  let elab_size e =
    let+ v = eval_const_int e in
    Texpr.int_ v ~ty:(Type.int_ ())

  (* File-scope attribute resolution: reuse the shared resolver (from
     [Elab_stmt]) with the file-scope constant-integer evaluator. *)
  let resolve_attrs (raws : A.ann Attr.raws) : Attr.set M.m =
    S.resolve_attrs ~eval_int:eval_const_int raws

  (* Redeclaration-aware registration of a function (§6.7 ¶4, §6.2.7):
     a re-declared name must have a type compatible with the first
     declaration.

     We keep the first registered type.
  *)
  let declare_func ~name ~ty =
    let* tenv = M.gets Ctx.tenv in
    match TE.find_func tenv name with
    | Some prev ->
      let* layout = M.gets Ctx.layout in
      let eval = Eval.create_init layout in
      M.unless (EC.compatible tenv eval prev ty) @@ fun () ->
      Ctx.fatal "conflicting types for '%s'" name ()
    | None -> Ctx.add_func ~name ~ty

  let declare_global ~name ~ty =
    let* tenv = M.gets Ctx.tenv in
    match TE.find_global tenv name with
    | Some prev ->
      let* layout = M.gets Ctx.layout in
      let eval = Eval.create_init layout in
      M.unless (EC.compatible tenv eval prev ty) @@ fun () ->
      Ctx.fatal "conflicting types for '%s'" name ()
    | None -> Ctx.add_global ~name ~ty

  (* §6.7 ¶3: a typedef name may be redefined, but (C11) only to denote the
     same type. GCC and Clang accept a compatible redefinition even in C99
     mode, and system headers rely on it, so accept it and reject only a
     conflicting redefinition. *)
  let declare_typedef ~name ~ty =
    let* tenv = M.gets Ctx.tenv in
    match TE.find_typedef tenv name with
    | None -> Ctx.add_typedef ~name ~ty
    | Some prev ->
      let* layout = M.gets Ctx.layout in
      let eval = Eval.create_init layout in
      M.unless (EC.compatible tenv eval prev ty) @@ fun () ->
      Ctx.fatal "conflicting types for typedef '%s'" name ()

  (* §6.8.1: labels are unique within a function.

     §6.8.6.1: every `goto` target must be a label defined in the
               enclosing function.
  *)
  let check_labels ~labaddrs body =
    let defined, used = collect_labels ([], []) body in
    let* () = match List.find_a_dup defined ~compare:String.compare with
      | Some l -> Ctx.fatal "duplicate label '%s'" l ()
      | None -> !!() in
    let dset = String.Set.of_list defined in
    let* () =
      M.List.map used ~f:(fun g ->
          M.unless (Set.mem dset g) @@ fun () ->
          Ctx.fatal "use of undeclared label '%s'" g ()) >>| ignore in
    (* Each address-taken label (`&&L`) must denote a label defined in this
       function. Cross-function label addresses are not supported. Report at
       the `&&L` site, captured when the address was first taken. *)
    M.List.map labaddrs ~f:(fun (g, loc) ->
        M.unless (Set.mem dset g) @@ fun () ->
        Ctx.with_location loc @@ fun () ->
        Ctx.fatal "address taken of undeclared label '%s'" g ()) >>| ignore

  (* Elaborate a struct/union field (§6.7.2.1).

     The field type is normalized (typedefs expanded) because a complete
     struct/union is laid out eagerly when its tag is registered, and
     `Layout` requires typedef-free types.

     Other type sinks (globals, locals) defer layout and normalize on
     demand via `Elab_conv`.
  *)
  let elab_field (f : A.ann Tydecl.field) =
    let* fty = ET.elab ~elab_size f.fty in
    let* tenv = M.gets Ctx.tenv in
    let fty = Elab_type.normalize tenv fty in
    let* fbits = match f.fbits with
      | None -> !!None
      | Some e ->
        let+ v = eval_const_int e in
        Some (Bv.to_int v) in
    let+ attrs = resolve_attrs f.fattrs in
    Tdecl.field ?bits:fbits ~attrs ~name:f.fname ~ty:fty ()

  (* Elaborate the enumerators of an `enum` (§6.7.2.2), threading the
     next implicit value and registering each constant. *)
  let elab_enum_items ~tag items =
    let rec go next acc = function
      | [] -> !!(List.rev acc)
      | (it : A.ann Tydecl.eitem) :: rest ->
        let* value = match it.eivalue with
          | None -> !!next
          | Some e ->
            let+ v = eval_const_int e in
            Bv.to_int64 v in
        let* () = Ctx.add_enum_element ~name:it.einame ~tag ~value in
        go (Int64.succ value) ((it.einame, value) :: acc) rest in
    go 0L [] items

  (* Build the typed parameter representations shared by a prototype and
     a definition.

     Returns, per parameter, its (optional) name and its decayed type.
  *)
  let elab_params params =
    let* tenv = M.gets Ctx.tenv in
    M.List.map params ~f:(fun (p : A.ann Decl.param) ->
        let+ pty = ET.elab ~elab_size p.pty in
        p.pname, param_decay tenv pty)

  let tdecl_params eparams =
    List.map eparams ~f:(fun (pn, pty) ->
        Tdecl.param ~name:(Option.value pn ~default:"") ~ty:pty)

  (* Elaborate a type declaration, registering it in the current scope. *)
  let elab_tydecl (td : A.ann Tydecl.t) : Tdecl.t option M.m =
    let@ () = Ctx.with_location_of td.Tydecl.ann in
    match td.Tydecl.node with
    | Tydecl.Typedef {name; ty} ->
      let* ty = ET.elab ~elab_size ty in
      let+ () = declare_typedef ~name ~ty in
      None
    | Tydecl.Compound {kind; tag; fields = None; attrs} ->
      (* A forward declaration (`struct S;`) registers an incomplete tag and
         produces no IR named type; it has no layout to lower. *)
      let* attrs = resolve_attrs attrs in
      let+ _disp =
        Ctx.add_tag ~name:tag @@
        TE.Tcompound {kind; fields = None; attrs} in
      None
    | Tydecl.Compound {kind; tag; fields = Some fields; attrs} ->
      let* attrs = resolve_attrs attrs in
      (* Bring the tag into scope as incomplete before its fields, so a
         self-referential member (`struct S { struct S *next; }`) resolves
         to this very tag rather than an enclosing one it may shadow. The
         second registration completes it, keeping the same display name. *)
      let* disp =
        Ctx.add_tag ~name:tag @@
        TE.Tcompound {kind; fields = None; attrs} in
      let* fields = M.List.map fields ~f:elab_field in
      let+ _disp =
        Ctx.add_tag ~name:tag @@
        TE.Tcompound {kind; fields = Some fields; attrs} in
      Some (Tdecl.compound ~kind ~tag:disp ~fields)
    | Tydecl.Enum {tag; items} ->
      let* pairs = elab_enum_items ~tag items in
      let+ _disp = Ctx.add_tag ~name:tag (TE.Tenum pairs) in
      None

  let elab_fundef
      ~name
      ~variadic
      ~ret_ty
      ~linkage
      ~inline
      ~noreturn
      ~attrs
      ~eparams
      body =
    (* §6.9.1 ¶5: parameter names may not be omitted in a definition. *)
    let* () = M.List.iter eparams ~f:(fun (pn, _) ->
        M.when_ (Option.is_none pn) @@ fun () ->
        Ctx.fatal "parameter name omitted in function definition" ()) in
    let* saved_fnctx = M.gets fnctx in
    let* saved_layout = M.gets layout in
    let* saved_statics = M.gets statics in
    let* () =
      M.update @@ fun c ->
      {c with fnctx = Some (Elab_ctx.create_fnctx ~fname:name ~retty:ret_ty ())} in
    (* The parameters and the body's top level share one block scope,
       distinct from file scope, so a body-level tag may shadow a
       file-scope tag of the same name. `exit_block` (below, against
       `saved_layout`) pops it. *)
    let* () =
      M.update @@ fun c -> {c with layout = Layout.push_scope c.layout} in
    let* () = M.List.iter eparams ~f:(function
        | Some n, pty -> Ctx.add_local ~name:n ~ty:pty
        | None, _ -> !!()) in
    let* tbody =
      S.elab_fnbody
        ~elab_rval:E.elab_rval
        ~elab_void:E.elab_void
        ~elab_tydecl
        body in
    let* fc = M.gets fnctx in
    let tmps, labaddrs = match fc with
      | Some fc -> fc.tmps, Ftree.to_list fc.labaddr
      | None -> [], [] in
    let body = prepend_tmps tmps tbody in
    (* §5.1.2.2.3: reaching the closing brace of `main` is equivalent to
       `return 0`. Append it explicitly so the destructure pass emits a return
       for the fall-through path rather than a trap; if the body already
       returns on all paths the appended statement is simply dead. *)
    let body =
      if String.equal name "main" && Type.is_integer ret_ty then
        let value = Texpr.int_ Bv.zero ~ty:(Type.int_ ()) in
        let ret = Tstmt.return ~value () in
        Tstmt.block [
          Tstmt.bstmt body;
          Tstmt.bstmt ret;
        ]
      else body in
    let* () = check_labels ~labaddrs body in
    let+ () =
      M.update @@ fun c -> {
        c with
        fnctx = saved_fnctx;
        (* Keep struct/union/enum tags declared in the body (the lowering
           needs their layouts) while dropping its params, locals, enum
           constants, and typedefs. *)
        layout = Layout.exit_block ~saved:saved_layout c.layout;
        statics = saved_statics;
      } in
    Tdecl.fundef
      ~name ~variadic ~body ~linkage ~inline ~noreturn ~attrs
      ~labaddrs:(List.map labaddrs ~f:fst)
      ~params:(tdecl_params eparams)
      ~ret:ret_ty
      ()

  let elab_dfun
      ~name ~params ~variadic ~ret ~body ~storage ~inline ~noreturn ~attrs =
    let* ret_ty = ET.elab ~elab_size ret in
    let* eparams = elab_params params in
    let fn_params =
      List.map eparams ~f:(fun (pname, ptype) -> Type.{pname; ptype}) in
    let fn_ty = Type.fun_ ~result:ret_ty ~params:fn_params ~variadic () in
    let linkage = linkage_of storage in
    let* () = declare_func ~name ~ty:fn_ty in
    match body with
    | Some body ->
      elab_fundef
        ~name
        ~variadic
        ~ret_ty
        ~linkage
        ~inline
        ~noreturn
        ~attrs
        ~eparams
        body
    | None ->
      M.return @@ Tdecl.fundecl
        ~name ~variadic ~linkage ~attrs
        ~params:(tdecl_params eparams)
        ~ret:ret_ty
        ()

  let elab_dvar ~name ~ty ~init ~storage ~tls ~attrs =
    let* base_ty = ET.elab ~elab_size ty in
    let linkage = linkage_of storage in
    match init, storage with
    | None, SCextern ->
      let* () = declare_global ~name ~ty:base_ty in
      (* An `alias` attribute makes even an `extern` declaration a definition
         of the alias symbol (§ GCC), so keep it as a global to be emitted. *)
      begin match Attr.alias attrs with
        | Some _ -> M.return @@ Tdecl.global ~name ~ty:base_ty ~linkage ~tls ~attrs ()
        | None -> M.return @@ Tdecl.extern ~name ~ty:base_ty ~linkage ~tls ()
      end
    | None, _ ->
      (* A tentative definition (§6.9.2). *)
      let+ () = declare_global ~name ~ty:base_ty in
      Tdecl.global ~name ~ty:base_ty ~linkage ~tls ~attrs ()
    | Some i, _ ->
      (* The initializer of a static-storage object must be a constant
         expression (§6.7.8 ¶4); `require_const` makes `EI.elab` verify
         each scalar leaf and reject anything that is not.

         We elaborate under a scratch context; a valid constant
         initializer produces no side-effect prefix.
      *)
      let* cty, flat =
        let@ () = with_scratch_fnctx in
        let+ _pre, cty, flat =
          EI.elab ~require_const:true ~elab_rval:E.elab_rval ~ty:base_ty i in
        cty, flat in
      let+ () = declare_global ~name ~ty:cty in
      Tdecl.global ~name ~ty:cty ~init:flat ~linkage ~tls ~attrs ()

  let elab_decl (d : A.ann Decl.t) : Tdecl.t option M.m =
    let@ () = Ctx.with_location_of d.ann in
    match d.node with
    | Dtype td -> elab_tydecl td
    | Dvar {name; ty; init; storage; tls; attrs} ->
      let* attrs = resolve_attrs attrs in
      let* () = Ctx.record_attrs ~name ~attrs in
      elab_dvar ~name ~ty ~init ~storage ~tls ~attrs >>| Option.some
    | Dfun {
        name;
        params;
        variadic;
        ret;
        body;
        storage;
        inline;
        attrs;
      } ->
      let* attrs = resolve_attrs attrs in
      let* () = Ctx.record_attrs ~name ~attrs in
      elab_dfun
        ~name
        ~params
        ~variadic
        ~ret
        ~body
        ~storage
        ~inline
        ~noreturn:(Attr.noreturn attrs)
        ~attrs
      >>| Option.some
end
