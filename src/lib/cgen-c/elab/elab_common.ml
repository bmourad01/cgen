open Core

module Bv = Cgen.Bv

let (let@) f x = f x

let pp_ty = Type.pp_with Texpr.pp

let stmt_is_empty = function
  | Tstmt.Sinstr [] | Tstmt.Sblock [] -> true
  | _ -> false

(* Zero of a scalar type, written `(T)0`: a plain zero for arithmetic
   types and a null pointer for pointer types, so the single form
   covers both. *)
let scalar_zero ty =
  Texpr.cast ~dst:ty ~arg:(Texpr.int_ Bv.zero ~ty:(Type.int_ ()))

let is_string_expr (e : _ Expr.t) = match e.node with
  | Econst Cstr _ -> true
  | _ -> false

let string_of_expr (e : _ Expr.t) = match e.node with
  | Econst Cstr s -> s
  | _ -> invalid_arg "Elab_common.string_of_expr: not a string literal"

let string_of_expr_opt e = Option.try_with @@ fun () -> string_of_expr e

let mkblock items =
  let rec splice acc = function
    | [] -> List.rev acc
    | Tstmt.Bstmt Sblock inner :: rest ->
      splice (List.rev_append inner acc) rest
    | item :: rest -> splice (item :: acc) rest in
  match splice [] items with
  | [Tstmt.Bstmt s] -> s
  | items -> Tstmt.Sblock items

module type Annotation = sig
  type ann
end
