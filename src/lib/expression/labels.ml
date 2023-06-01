open Core
open Virtual
open Common

let rec labels_of_pure = function
  | Palloc (l, _) -> Label.Set.singleton l
  | Pbinop (l, _, a, b) ->
    let a = labels_of_pure a in
    let b = labels_of_pure b in
    Set.(add (union a b) l)
  | Pcall (l, _, f, args, vargs) ->
    let f = labels_of_global f in
    let args = List.map args ~f:labels_of_pure in
    let vargs = List.map vargs ~f:labels_of_pure in
    Label.Set.(add (union_list (f :: (args @ vargs))) l)
  | Pdouble _ | Pflag _ | Pint _ | Psingle _ | Psym _ | Pvar _ ->
    Label.Set.empty
  | Pload (l, _, a) -> Set.(add (labels_of_pure a) l)
  | Psel (l, _, c, t, f) ->
    let c = labels_of_pure c in
    let t = labels_of_pure t in
    let f = labels_of_pure f in
    Label.Set.(add (union_list [c; t; f]) l)
  | Punop (l, _, a) -> Set.(add (labels_of_pure a) l)

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
