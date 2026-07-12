(* Elaboration of types: `'a Expr.ty` to `Texpr.ty`.

   The structure of the type is preserved (including typedef
   references, which can be expanded on demand via `normalize`).

   Array sizes are elaborated via the `elab_size` callback supplied
   by the caller, which produces a `Texpr.t`.

   C99 requires the size of a non-VLA array to be an integer
   constant expression. The actual ICE fold happens in the caller
   using `Eval.int_const`.
*)

open Core
open Elab_common

module TE = Type_env

let tag_keyword : Type.tag -> string = function
  | `struct_ -> "struct"
  | `union   -> "union"
  | `enum    -> "enum"

let named ~cv (kind : Type.tag) name = match kind with
  | `struct_ -> Type.struct_ ~cv name
  | `union   -> Type.union_  ~cv name
  | `enum    -> Type.enum_   ~cv name

let normalize = TE.normalize

module Make(A : Annotation) = struct
  module Ctx = Elab_ctx.Make(A)

  open Ctx
  open Syntax

  (* Resolve a tag reference to the display name it denotes, declaring it
     when necessary.

     A `struct`/`union` tag that is not (yet) visible denotes an incomplete
     type (a forward reference), which is legal in C. Examples include:

     - opaque types,
     - mutually recursive structs through pointers
     - `typedef struct S T;` before `struct S` is defined

     We declare such a tag incomplete on first reference so its identity is
     stable. A later completion (or another reference) resolves to the same
     tag. Completeness is only required where the type is actually used (an
     object definition, `sizeof`, member access) and is checked at those
     sites. An `enum` tag, which cannot be left incomplete, must already be
     defined.
  *)
  let resolve_tag ~kind ~name =
    let* env = M.gets Ctx.tenv in
    match TE.resolve_tag env name with
    | Some disp -> !!disp
    | None -> match kind with
      | `enum -> Ctx.fatal "undefined %s tag '%s'" (tag_keyword kind) name ()
      | #Type.compound as kind ->
        Ctx.add_tag ~name @@
        TE.Tcompound {kind; fields = None; attrs = Attr.empty}

  (* Look up a typedef and emit a diagnostic if it isn't bound. *)
  let check_typedef ~name =
    let* env = M.gets Ctx.tenv in
    M.unless (TE.has_typedef env name) @@ fun () ->
    Ctx.fatal "undefined typedef '%s'" name ()

  (* Walk a type, threading the `elab_size` callback through arrays. *)
  let elab ~elab_size =
    let rec go : A.ann Expr.ty -> _ = function
      | Tbase {base; cv} ->
        !!(Type.Tbase {base; cv})
      | Tnamed {kind = `typedef; name; cv} ->
        let+ () = check_typedef ~name in
        Type.typedef_ ~cv name
      | Tnamed {kind = #Type.tag as kind; name; cv} ->
        (* Resolve the source tag name to the display name it denotes in the
           current lexical scope; the elaborated type carries that name so
           the lowering resolves it directly. *)
        let+ disp = resolve_tag ~kind ~name in
        named ~cv kind disp
      | Tptr {pointee; restrict; cv} ->
        let+ pointee = go pointee in
        Type.ptr ~cv ~restrict pointee
      | Tarray {elem; size = None; cv} ->
        let+ elem = go elem in
        Type.array ~cv elem
      | Tarray {elem; size = Some e; cv} ->
        let* elem = go elem in
        let+ size = elab_size e in
        Type.array ~cv ~size elem
      | Tfun {result; params = None; _} ->
        let+ result = go result in
        Type.fun_kr result
      | Tfun {result; params = Some ps; variadic} ->
        let* result = go result in
        let+ params =
          M.List.map ps ~f:(fun (p : A.ann Expr.t Type.param) ->
              let+ ptype = go p.ptype in
              Type.{pname = p.pname; ptype}) in
        Type.fun_ ~result ~params ~variadic () in
    go
end
