open Core

let var_set_of_option = function
  | Some x -> Var.Set.singleton x
  | None -> Var.Set.empty

type 'a ftree = 'a Ftree.t [@@deriving bin_io, sexp]

let compare_ftree compare t1 t2 = Ftree.compare t1 t2 ~compare
let equal_ftree equal t1 t2 = Ftree.equal t1 t2 ~equal

module Ftree = struct
  include Ftree

  let index_of xs f i =
    Ftree.findi xs ~f:(fun _ x -> f x i) |> Option.map ~f:fst

  (* Insert an element before a specific element of the tree. *)
  let cons' ?(before = None) xs x f = match before with
    | None -> Ftree.cons xs x
    | Some i -> match index_of xs f i with
      | Some i -> Ftree.insert xs x i
      | None -> xs

  (* Same as above, but for a list of elements. *)
  let multi_cons' ?(before = None) xs ys f = match ys with
    | [] -> xs
    | [y] -> cons' ~before xs y f
    | _ -> match before with
      | None -> append (of_list ys) xs
      | Some i -> match index_of xs f i with
        | None -> xs
        | Some i ->
          let xs, xs' = split_at_exn xs i in
          append xs @@ append (of_list ys) xs'

  (* Insert an element after a specific element of the tree. *)
  let snoc' ?(after = None) xs x f = match after with
    | None -> Ftree.snoc xs x
    | Some i -> match index_of xs f i with
      | Some i -> Ftree.insert xs x (i + 1)
      | None -> xs

  (* Same as above, but for a list of elements. *)
  let multi_snoc' ?(after = None) xs ys f = match ys with
    | [] -> xs
    | [y] -> snoc' ~after xs y f
    | _ -> match after with
      | None -> append xs @@ of_list ys
      | Some i -> match index_of xs f i with
        | None -> xs
        | Some i ->
          let xs, xs' = split_at_exn xs (i + 1) in
          append xs @@ append (of_list ys) xs'

  let remove xs i f = Ftree.remove_if xs ~f:(Fn.flip f i)
end

type const = [
  | `bool   of bool
  | `int    of Bv.t * Type.imm
  | `float  of Float32.t
  | `double of float
  | `sym    of string * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_const ppf : const -> unit = function
  | `bool f -> Format.fprintf ppf "%a" Bool.pp f
  | `int (n, t) -> Format.fprintf ppf "%a_%a" Bv.pp n Type.pp_imm t
  | `float f -> Format.fprintf ppf "%s_f" @@ Float32.to_string f
  | `double d -> Format.fprintf ppf "%a_d" Float.pp d
  | `sym (s, 0) -> Format.fprintf ppf "$%s" s
  | `sym (s, n) when n > 0 -> Format.fprintf ppf "$%s+0x%x" s n
  | `sym (s, n) -> Format.fprintf ppf "$%s-0x%x" s (lnot n + 1)

type operand = [
  | const
  | `var of Var.t
] [@@deriving bin_io, compare, equal, hash, sexp]

let var_of_operand = function
  | `var v -> Some v
  | _ -> None

let pp_operand ppf : operand -> unit = function
  | #const as c -> Format.fprintf ppf "%a" pp_const c
  | `var v -> Format.fprintf ppf "%a" Var.pp v

type global = [
  | `addr of Bv.t
  | `sym  of string * int
  | `var  of Var.t
] [@@deriving bin_io, compare, equal, sexp]

let var_of_global : global -> Var.t option = function
  | `var x -> Some x
  | `addr _ | `sym _ -> None

let pp_global ppf : global -> unit = function
  | `addr a -> Format.fprintf ppf "%a" Bv.pp a
  | `sym (s, 0) -> Format.fprintf ppf "$%s" s
  | `sym (s, o) when o > 0 -> Format.fprintf ppf "$%s+%d" s o
  | `sym (s, o) -> Format.fprintf ppf "$%s-%d" s (lnot o + 1)
  | `var v -> Format.fprintf ppf "%a" Var.pp v

type local = [
  | `label of Label.t * operand list
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_local : local -> Var.Set.t = function
  | `label (_, args) ->
    List.fold args ~init:Var.Set.empty ~f:(fun s -> function
        | `var v -> Set.add s v
        | _ -> s)

let pp_local ppf : local -> unit = function
  | `label (l, []) -> Format.fprintf ppf "%a" Label.pp l
  | `label (l, args) ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    Format.fprintf ppf "%a(%a)"
      Label.pp l (Format.pp_print_list ~pp_sep pp_operand) args

type dst = [
  | global
  | local
] [@@deriving bin_io, compare, equal, sexp]

let free_vars_of_dst : dst -> Var.Set.t = function
  | `var x -> Var.Set.singleton x
  | #local as l -> free_vars_of_local l
  | _ -> Var.Set.empty

let pp_dst ppf : dst -> unit = function
  | #global as g -> Format.fprintf ppf "%a" pp_global g
  | #local  as l -> Format.fprintf ppf "%a" pp_local l
