open Core
open Cgen_utils

let elab
    (type a)
    ?(loc_of_ann = (fun _ -> None : a -> Location.t option))
    (cunit : a Cunit.t)
    ~dmodel
  : (Tcunit.t * Diagnostic.t list, Diagnostic.t) result =
  let module A = struct type ann = a end in
  let module D = Elab_decl.Make(A) in
  let module Ctx = D.Ctx in
  let open Ctx.Syntax in
  let comp =
    (* Seed the compiler builtin typedef `__builtin_va_list` (the type
       `<stdarg.h>` aliases as `va_list`) with the target's layout. *)
    let* () = Ctx.add_typedef ~name:"__builtin_va_list" ~ty:(Data_model.va_list dmodel) in
    let* opts = Ctx.M.List.map (Cunit.decls cunit) ~f:D.elab_decl in
    (* Block-scope statics are hoisted to module-level globals during
       function elaboration; append them in source order. *)
    let* hoisted = Ctx.M.gets Ctx.hoisted in
    let* layout = Ctx.M.gets Ctx.layout in
    let decls = List.filter_opt opts @ List.rev hoisted in
    (* §6.9.2: a file-scope object definition may be a tentative definition
       with an incomplete type, provided the type is completed by the end of
       the unit. Check the final environment now that every tag is known. *)
    let tenv = Layout.tenv layout in
    let+ () = Ctx.M.List.iter decls ~f:(function
        | Tdecl.Dglobal {name; ty; attrs; _}
          when Option.is_none (Attr.alias attrs) ->
          begin match Type_env.incomplete_object_type tenv ty with
            | None -> Ctx.M.return ()
            | Some tag ->
              Ctx.fatal
                "'%s' has incomplete type (struct/union '%s' is never defined)"
                name tag ()
          end
        | _ -> Ctx.M.return ()) in
    Tcunit.create ~decls ~layout in
  Ctx.M.run comp
    ~init:(Ctx.create ~dmodel ~loc_of_ann)
    ~reject:(fun e -> Error e)
    ~accept:(fun u s -> Ok (u, Ctx.warnings s))
