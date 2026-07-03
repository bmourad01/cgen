(* Elaborator state *)

open Core
open Cgen_utils
open Elab_common

module Ftree = Cgen_containers.Ftree

type fnctx = {
  retty   : Texpr.ty;
  fresh   : int;
  tmps    : Tstmt.localdecl list;
  labaddr : (string * Location.t option) Ftree.t;
}

let create_fnctx ~retty = {
  retty;
  fresh = 0;
  tmps = [];
  labaddr = Ftree.empty;
}

let index_of_labaddr c name =
  Ftree.index c.labaddr ~f:(fun (n, _) -> String.(n = name))

module Make(A : Annotation) = struct
  type ann = A.ann

  type t = {
    layout       : Layout.t;
    location     : Location.t option;
    loc_of_ann   : ann -> Location.t option;
    fnctx        : fnctx option;
    statics      : string String.Map.t;
    hoisted      : Tdecl.t list;
    static_count : int;
    warnings     : Diagnostic.t list;
  }

  let create ~dmodel ~loc_of_ann = {
    layout = Layout.empty ~dmodel;
    location = None;
    loc_of_ann;
    fnctx = None;
    statics = String.Map.empty;
    hoisted = [];
    static_count = 0;
    warnings = [];
  }

  let layout t = t.layout
  let tenv t = Layout.tenv t.layout
  let dmodel t = Layout.dmodel t.layout
  let location t = t.location
  let fnctx t = t.fnctx
  let statics t = t.statics
  let static_link name t = Map.find t.statics name
  let hoisted t = t.hoisted

  (* Warnings raised during elaboration, in source order. *)
  let warnings t = List.rev t.warnings

  (* The return type of the enclosing function, if any. *)
  let return_ty t = Option.map t.fnctx ~f:(fun fc -> fc.retty)

  module M = Cgen_utils.Sm.Make(struct
      type state = t
      type error = Diagnostic.t
      let of_or_error = Diagnostic.of_error
    end)

  let lift_err ?prefix e =
    let open M.Syntax in
    match e with
    | Ok x -> !!x
    | Error e ->
      let e = match prefix with
        | None -> e
        | Some p -> Error.tag e ~tag:p in
      let* loc = M.gets location in
      M.fail (Diagnostic.error ?location:loc (Error.to_string_hum e))

  module Syntax = struct
    include M.Syntax

    let (>>?) x f = lift_err x >>= f
    let (>|?) x f = lift_err x >>| f
    let (let*?) x f = x >>? f
    let (let+?) x f = x >|? f
  end

  open Syntax

  let tmp_name n = Format.sprintf "%%%d" n

  let fresh_tlval ?init ty =
    let* ctx = M.get () in
    match ctx.fnctx with
    | None -> failwith "Elab_ctx.fresh_tlval: no enclosing function context"
    | Some fc ->
      let name = tmp_name fc.fresh in
      let tmp  = Tstmt.{name; ty; init} in
      let fc' = {fc with fresh = fc.fresh + 1; tmps = tmp :: fc.tmps} in
      let+ () = M.put {ctx with fnctx = Some fc'} in
      Texpr.lvar name ~ty

  (* The integer index of a label whose address is taken (`&&name`),
     assigning it the next index the first time it is seen. *)
  let labaddr_index name =
    let* ctx = M.get () in
    match ctx.fnctx with
    | None -> failwith "Elab_ctx.labaddr_index: no enclosing function context"
    | Some fc -> match index_of_labaddr fc name with
      | Some i -> !!i
      | None ->
        let i = Ftree.length fc.labaddr in
        let entry = name, ctx.location in
        let fc' = {fc with labaddr = Ftree.snoc fc.labaddr entry} in
        let+ () = M.put {ctx with fnctx = Some fc'} in
        i

  let fresh_label =
    let* ctx = M.get () in
    match ctx.fnctx with
    | None -> failwith "Elab_ctx.fresh_label: no enclosing function context"
    | Some fc ->
      let name = tmp_name fc.fresh in
      let+ () = M.put {ctx with fnctx = Some {fc with fresh = fc.fresh + 1}} in
      name

  (* Run `f` with `loc` installed as the current diagnostic location,
     restoring the prior location on exit. *)
  let with_location loc f =
    let* prev = M.gets location in
    let* () = M.update @@ fun ctx -> {ctx with location = loc} in
    let* result = f () in
    let+ () = M.update @@ fun ctx -> {ctx with location = prev} in
    result

  let with_location_of ann f =
    let* ctx = M.get () in
    with_location (ctx.loc_of_ann ann) f

  (* Run `f`, then roll back the temporary allocator (`fnctx`) to
     its prior state, dropping any temporaries `f` reserved.

     For unevaluated operands (e.g. the operand of `sizeof`): we only
     want `f`'s result, not the temps a dry elaboration would leave
     behind. Local bindings in `layout` are not scoped here.
  *)
  let discarding_temps f =
    let* saved = M.gets fnctx in
    let* result = f () in
    let+ () = M.update @@ fun ctx -> {ctx with fnctx = saved} in
    result

  (* Run `f` in a nested block scope.

     A fresh innermost scope is pushed for `f`, so the locals it binds
     shadow (rather than collide with) those of enclosing scopes. The
     scope is dropped on exit by restoring the pre-push `layout`, which
     also discards any block-local tags and typedefs `f` introduced.

     Temporaries in `fnctx` that are hoisted to the function top during
     `f` are kept.

     This function is the dual of `discarding_temps`.
  *)
  let with_block_scope f =
    let* saved_layout = M.gets layout in
    let* saved_statics = M.gets statics in
    let* () = M.update @@ fun ctx ->
      {ctx with layout = Layout.push_scope ctx.layout} in
    let* result = f () in
    let+ () =
      M.update @@ fun ctx -> {
        ctx with
        layout = saved_layout;
        statics = saved_statics;
      } in
    result

  let fatal fmt =
    let buf = Buffer.create 256 in
    let ppf = Format.formatter_of_buffer buf in
    let kon ppf () =
      Format.pp_print_flush ppf ();
      let msg = Buffer.contents buf in
      let* loc = M.gets location in
      M.fail (Diagnostic.error ?location:loc msg) in
    Format.kfprintf kon ppf fmt

  (* Accumulate a non-fatal diagnostic; elaboration continues. *)
  let warn d = M.update @@ fun ctx -> {ctx with warnings = d :: ctx.warnings}

  (* Emit a warning at the current location. *)
  let warnf fmt =
    let buf = Buffer.create 256 in
    let ppf = Format.formatter_of_buffer buf in
    let kon ppf () =
      Format.pp_print_flush ppf ();
      let msg = Buffer.contents buf in
      let* loc = M.gets location in
      warn (Diagnostic.warning ?location:loc msg) in
    Format.kfprintf kon ppf fmt

  (* Emit an optional pre-formatted warning message (produced by a pure
     helper that lacks location context) at the current location. *)
  let warn_opt = function
    | None -> !!()
    | Some msg ->
      let* loc = M.gets location in
      warn (Diagnostic.warning ?location:loc msg)

  (* Bind a local variable (or parameter) in the innermost scope.

     Rejects a redeclaration of a name already bound in that same
     scope (C99 §6.7 ¶3); shadowing a name from an enclosing scope is
     permitted.
  *)
  let add_local ~name ~ty =
    let* ctx = M.get () in
    let*? layout = Layout.strict_add_local ctx.layout ~name ty in
    (* A plain local shadows any static/extern alias of the same name in
       an enclosing scope; the alias is restored when this scope exits. *)
    M.put {ctx with layout; statics = Map.remove ctx.statics name}

  (* Alias a block-scope source name to the link symbol that references
     should resolve to (see the `statics` field). *)
  let add_static_alias ~name ~link = M.update @@ fun ctx ->
    {ctx with statics = Map.set ctx.statics ~key:name ~data:link}

  (* A fresh, unit-unique symbol for a block-scope static. The `.` keeps
     it from colliding with any C-identifier-derived symbol. *)
  let fresh_static_sym ~source =
    let* ctx = M.get () in
    let n = ctx.static_count in
    let+ () = M.put {ctx with static_count = n + 1} in
    Format.sprintf "%s.%d" source n

  (* Queue a module-level definition (from a block-scope static). *)
  let hoist_global decl = M.update @@ fun ctx ->
    {ctx with hoisted = decl :: ctx.hoisted}

  (* File-scope environment writers.

     Each forwards to the matching `Layout` mutator, which keeps the
     layout maps in lockstep with the tenv.
  *)

  let add_tag ~name tag =
    let* ctx = M.get () in
    let* layout = lift_err @@ Layout.add_tag ctx.layout ~name tag in
    M.put {ctx with layout}

  let add_enum_element ~name ~tag ~value =
    let* ctx = M.get () in
    let*? layout = Layout.add_enum_element ctx.layout ~name ~tag ~value in
    M.put {ctx with layout}

  let add_typedef ~name ~ty =
    let* ctx = M.get () in
    let*? layout = Layout.add_typedef ctx.layout ~name ty in
    M.put {ctx with layout}

  let add_func ~name ~ty =
    let* ctx = M.get () in
    let*? layout = Layout.add_func ctx.layout ~name ty in
    M.put {ctx with layout}

  let add_global ~name ~ty =
    let* ctx = M.get () in
    let*? layout = Layout.add_global ctx.layout ~name ty in
    M.put {ctx with layout}
end
