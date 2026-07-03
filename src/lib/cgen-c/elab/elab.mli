(** C elaboration: untyped surface AST to typed AST.

    The elaborator takes a parsed (untyped) translation unit and
    produces the fully-typed [Tcunit.t] with all C99 elaboration
    performed: name resolution, type checking, implicit conversions,
    lvalue/rvalue distinction, side-effect extraction, designated-
    initializer flattening, and constant folding.

    Errors are returned as structured {!Cgen_utils.Diagnostic.t} values.
    Callers that prefer the [Or_error.t] form can convert via
    {!Cgen_utils.Diagnostic.to_error}.
*)

open Cgen_utils

(** [elab ?loc_of_ann u ~dmodel] elaborates the translation unit [u]
    under the target [dmodel].

    [loc_of_ann] extracts a source location from each AST node's
    annotation; if omitted, diagnostics carry no location information.

    On success, returns the typed unit together with the non-fatal
    warnings accumulated during elaboration, in source order.

    A fatal error short-circuits elaboration and is returned as [Error];
    any warnings raised before it are not reported.
*)
val elab :
  ?loc_of_ann:('a -> Location.t option) ->
  'a Cunit.t ->
  dmodel:Data_model.t ->
  (Tcunit.t * Diagnostic.t list, Diagnostic.t) result
