open Core
open Common

let label_opt = function
  | None -> Label.Set.empty
  | Some l -> Label.Set.singleton l

let rec labels_of_args args =
  List.map args ~f:labels_of_pure |>
  Label.Set.union_list

and labels_of_pure = function
  | Palloc (l, _) -> label_opt l
  | Pbinop (l, _, a, b) ->
    Label.Set.union_list [
      label_opt l;
      labels_of_pure a;
      labels_of_pure b;
    ]
  | Pcall (l, _, f, args, vargs) ->
    Label.Set.union_list [
      label_opt l;
      labels_of_global f;
      labels_of_args args;
      labels_of_args vargs;
    ]
  | Pbool _ | Pdouble _ | Pint _ | Psingle _ | Psym _ | Pvar _ ->
    Label.Set.empty
  | Pload (l, _, a) ->
    Label.Set.union_list [
      label_opt l;
      labels_of_pure a;
    ]
  | Psel (l, _, c, t, f) ->
    Label.Set.union_list [
      label_opt l;
      labels_of_pure c;
      labels_of_pure t;
      labels_of_pure f;
    ]
  | Punop (l, _, a) ->
    Label.Set.union_list [
      label_opt l;
      labels_of_pure a;
    ]

and labels_of_global = function
  | Gaddr _ | Gsym _ -> Label.Set.empty
  | Gpure p -> labels_of_pure p

let labels_of_local (_, args) =
  List.map args ~f:labels_of_pure |>
  Label.Set.union_list

let labels_of_dst = function
  | Dglobal g -> labels_of_global g
  | Dlocal l -> labels_of_local l

let labels_of_table tbl =
  List.map tbl ~f:(fun (_, l) -> labels_of_local l) |>
  Label.Set.union_list

let labels = function
  | Ebr (c, t, f) ->
    Label.Set.union_list [
      labels_of_pure c;
      labels_of_dst t;
      labels_of_dst f;
    ]
  | Ecall (f, args, vargs) ->
    let f = labels_of_global f in
    let args = List.map args ~f:labels_of_pure in
    let vargs = List.map vargs ~f:labels_of_pure in
    Label.Set.union_list (f :: (args @ vargs))
  | Ehlt | Eret None | Evaarg _ | Evastart _ -> Label.Set.empty
  | Ejmp d -> labels_of_dst d
  | Eret (Some p) | Eset (_, p) -> labels_of_pure p
  | Estore (_, v, a) ->
    Set.union (labels_of_pure v) (labels_of_pure a)
  | Esw (_, i, d, tbl) ->
    Label.Set.union_list [
      labels_of_pure i;
      labels_of_local d;
      labels_of_table tbl;
    ]
