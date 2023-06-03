open Core
open Common

let rec free_vars_of_pure = function
  | Palloc _ | Pbool _ | Pdouble _ | Pint _ | Psingle _ | Psym _ ->
    Var.Set.empty
  | Pbinop (_, _, a, b) ->
    Set.union (free_vars_of_pure a) (free_vars_of_pure b)
  | Pcall (_, _, f, args, vargs) ->
    let args = List.map args ~f:free_vars_of_pure in
    let vargs = List.map vargs ~f:free_vars_of_pure in
    Var.Set.union_list (free_vars_of_global f :: (args @ vargs))
  | Pload (_, _, a) | Punop (_, _, a) -> free_vars_of_pure a
  | Psel (_, _, c, t, f) ->
    Var.Set.union_list [
      free_vars_of_pure c;
      free_vars_of_pure t;
      free_vars_of_pure f;
    ]
  | Pvar v -> Var.Set.singleton v

and free_vars_of_global = function
  | Gaddr _ | Gsym _ -> Var.Set.empty
  | Gpure p -> free_vars_of_pure p

let free_vars_of_local (_, args) =
  List.map args ~f:free_vars_of_pure |> Var.Set.union_list

let free_vars_of_dst = function
  | Dglobal g -> free_vars_of_global g
  | Dlocal l -> free_vars_of_local l

let free_vars_of_table tbl =
  List.map tbl ~f:(fun (_, l) -> free_vars_of_local l) |>
  Var.Set.union_list

let free_vars = function
  | Ebr (c, t, f) ->
    Var.Set.union_list [
      free_vars_of_pure c;
      free_vars_of_dst t;
      free_vars_of_dst f;
    ]
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:free_vars_of_pure in
    let vargs = List.map vargs ~f:free_vars_of_pure in
    Var.Set.union_list (free_vars_of_global f :: (args @ vargs))
  | Ehlt | Eret None -> Var.Set.empty
  | Ejmp d -> free_vars_of_dst d
  | Eret (Some p) | Eset (_, p) -> free_vars_of_pure p
  | Estore (_, v, a) ->
    Set.union (free_vars_of_pure v) (free_vars_of_pure a)
  | Esw (_, i, d, tbl) ->
    Var.Set.union_list [
      free_vars_of_pure i;
      free_vars_of_local d;
      free_vars_of_table tbl;
    ]
  | Evaarg (_, _, v) | Evastart v -> Var.Set.singleton v
