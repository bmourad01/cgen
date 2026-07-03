(** Efficient state + error monad.

    The monadic type is a single CPS function that takes a state plus
    [reject] and [accept] continuations, avoiding any per-bind allocation
    of [Result.t] cells.

    Parameterized over the user's [error] type via [S.of_or_error], so
    different callers can attach their own structured errors (e.g. a
    diagnostic record with source location) instead of bare strings.
*)

open Core
open Monads.Std

module type S = sig
  type state
  type error

  (** Lift an [Error.t] (used internally by [failf] and [lift_err])
      into the user's error type. *)
  val of_or_error : Error.t -> error
end

module Make(M : S) = struct
  type 'a m = {
    run : 'r. reject:(M.error -> 'r) -> accept:('a -> M.state -> 'r) -> M.state -> 'r;
  }

  let fail (err : M.error) = {
    run = fun ~reject ~accept:_ _ -> reject err
  } [@@inline]

  let failf fmt =
    let buf = Buffer.create 512 in
    let ppf = Format.formatter_of_buffer buf in
    let kon ppf () =
      Format.pp_print_flush ppf ();
      let err = Error.of_string (Buffer.contents buf) in
      fail (M.of_or_error err) in
    Format.kfprintf kon ppf fmt

  module SM = Monad.Make(struct
      type 'a t = 'a m

      let return x = {
        run = fun ~reject:_ ~accept s -> accept x s
      } [@@inline]

      let bind x f = {
        run = fun ~reject ~accept s ->
          x.run s ~reject ~accept:(fun x s ->
              (f x).run ~reject ~accept s)
      } [@@inline]

      let map x ~f = {
        run = fun ~reject ~accept s ->
          x.run s ~reject ~accept:(fun x s -> accept (f x) s)
      } [@@inline]

      let map = `Custom map
    end)

  include SM

  let lift_err ?prefix : 'a Or_error.t -> 'a m = function
    | Ok x -> return x
    | Error err ->
      let err = match prefix with
        | None -> err
        | Some p -> Error.tag err ~tag:p in
      fail (M.of_or_error err)

  module Syntax = struct
    include SM.Syntax
    include SM.Let

    let (>>?) x f = lift_err x >>= f
    let (>|?) x f = lift_err x >>| f
    let (let*?) x f = x >>? f
    let (let+?) x f = x >|? f

    let (and+) x y = {
      run = fun ~reject ~accept s ->
        x.run s ~reject ~accept:(fun x s ->
            y.run s ~reject ~accept:(fun y s ->
                accept (x, y) s))
    } [@@inline]

    let (and*) = (and+)
  end

  let get () = {
    run = fun ~reject:_ ~accept s -> accept s s
  } [@@inline]

  let put s = {
    run = fun ~reject:_ ~accept _ -> accept () s
  } [@@inline]

  let gets f = {
    run = fun ~reject:_ ~accept s -> accept (f s) s
  } [@@inline]

  let update f = {
    run = fun ~reject:_ ~accept s -> accept () (f s)
  } [@@inline]

  let when_ k f = if k then f () else !!() [@@inline]
  let unless k f = if k then !!() else f () [@@inline]

  let catch x err = {
    run = fun ~reject ~accept s ->
      x.run s ~accept ~reject:(fun p ->
          (err p).run ~reject ~accept s)
  } [@@inline]

  let run x ~init ~reject ~accept = x.run ~reject ~accept init

  module List = struct
    include List

    (* The derived `List.map` in the `Monads` library will accumulate
       and unwrap the monadic terms in reverse order, which is not what
       we want for generating fresh labels. *)
    let map l ~f =
      let rec aux l k = match l with
        | [] -> k []
        | x :: xs ->
          f x >>= fun y ->
          aux xs (fun ys -> k (y :: ys)) in
      aux l return

    let filter_map l ~f =
      let rec aux l k = match l with
        | [] -> k []
        | x :: xs ->
          f x >>= function
          | None -> aux xs k
          | Some y -> aux xs (fun ys -> k (y :: ys)) in
      aux l return

    let all = map ~f:Base.Fn.id
  end

  module Seq = struct
    include Seq

    (* Like the custom `List.map` above, accumulate in order via CPS rather
       than `Base.Sequence.append`, which is quadratic (each step nests an
       `append`, so forcing the result is O(n^2)). The monadic effects are
       run eagerly regardless. The result is a pure sequence, so every `f x`
       must run during this computation. *)
    let map s ~f =
      let rec aux s k = match Base.Sequence.next s with
        | None -> k []
        | Some (x, xs) ->
          f x >>= fun y ->
          aux xs (fun ys -> k (y :: ys)) in
      aux s (fun ys -> return @@ Base.Sequence.of_list ys)

    let filter_map s ~f =
      let rec aux s k = match Base.Sequence.next s with
        | None -> k []
        | Some (x, xs) ->
          f x >>= function
          | None -> aux xs k
          | Some y -> aux xs (fun ys -> k (y :: ys)) in
      aux s (fun ys -> return @@ Base.Sequence.of_list ys)

    let all = map ~f:Base.Fn.id
  end

  let map_list_err ?prefix l ~f = List.map l ~f:(Base.Fn.compose (lift_err ?prefix) f)
  let iter_list_err ?prefix l ~f = List.iter l ~f:(Base.Fn.compose (lift_err ?prefix) f)
  let map_seq_err ?prefix s ~f = Seq.map s ~f:(Base.Fn.compose (lift_err ?prefix) f)
  let iter_seq_err ?prefix s ~f = Seq.iter s ~f:(Base.Fn.compose (lift_err ?prefix) f)
end
