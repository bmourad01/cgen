open Core
open Monads.Std
open Regular.Std

module Bitvec = struct
  include Bitvec
  include Bitvec_binprot
  include Bitvec_order
  include Bitvec_sexp
end

let var_set_of_option = function
  | Some x -> Var.Set.singleton x
  | None -> Var.Set.empty

module Array = struct
  include Base.Array

  let insert xs x i = length xs |> succ |> init ~f:(fun j ->
      if j < i then xs.(j) else if j = i then x else xs.(j - 1))

  let push_back xs x = insert xs x @@ length xs
  let push_front xs x = insert xs x 0

  let remove_if xs ~f =
    if exists xs ~f then filter xs ~f:(Fn.non f) else xs

  let update_if xs y ~f =
    if exists xs ~f then map xs ~f:(fun x -> if f x then y else x) else xs

  let pp ppx sep ppf xs =
    let last = length xs - 1 in
    iteri xs ~f:(fun i x ->
        Format.fprintf ppf "%a" ppx x;
        if i < last then sep ppf)

  let findi_label xs f l = findi xs ~f:(fun _ x -> Label.equal l @@ f x)

  let next xs f l =
    let open Monad.Option.Syntax in
    findi_label xs f l >>= fun (i, _) ->
    if i = length xs - 1 then None else Some xs.(i + 1)

  let prev xs f l =
    let open Monad.Option.Syntax in
    findi_label xs f l >>= fun (i, _) ->
    if i = 0 then None else Some xs.(i - 1)

  let enum ?(rev = false) xs =
    let n = length xs in
    if not rev then Seq.init n ~f:(unsafe_get xs)
    else Seq.init n ~f:(fun i -> unsafe_get xs (n - i - 1))
end

type const = [
  | `int    of Bitvec.t
  | `float  of Float32.t
  | `double of float
  | `sym    of string * int
] [@@deriving bin_io, compare, equal, sexp]

let pp_const ppf : const -> unit = function
  | `int n -> Format.fprintf ppf "%a" Bitvec.pp n
  | `float f -> Format.fprintf ppf "%sf" @@ Float32.to_string f
  | `double d -> Format.fprintf ppf "%a" Float.pp d
  | `sym (s, 0) -> Format.fprintf ppf "$%s" s
  | `sym (s, n) when n > 0 -> Format.fprintf ppf "$%s+0x%x" s n
  | `sym (s, n) -> Format.fprintf ppf "$%s-0x%x" s (lnot n + 1)
