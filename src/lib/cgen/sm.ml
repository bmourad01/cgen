(* Efficient state + error monad. *)

open Core
open Monads.Std

module type S = sig
  type state
  val error_prefix : string
end

module Make(M : S) = struct
  type 'a m = {
    run : 'r. reject:(Error.t -> 'r) -> accept:('a -> M.state -> 'r) -> M.state -> 'r;
  }

  let fail err = {
    run = fun ~reject ~accept:_ _ -> reject err
  }

  let failf fmt =
    let buf = Buffer.create 512 in
    let ppf = Format.formatter_of_buffer buf in
    let kon ppf () =
      Format.pp_print_flush ppf ();
      let err =
        Error.createf "%s: %s" M.error_prefix @@
        Buffer.contents buf in
      fail err in
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
    | Error err -> match prefix with
      | None -> failf "%a" Error.pp err ()
      | Some p -> failf "%s: %a" p Error.pp err ()

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

  module List = struct
    include List

    (* The derived List.map in the Monads library will accumulate (and
       unwrap the monadic terms) in reverse order, which is not what we
       want for generating fresh labels. *)
    let map l ~f =
      fold l ~init:[] ~f:(fun acc x ->
          f x >>| Base.Fn.flip Base.List.cons acc) >>|
      Base.List.rev

    let all = map ~f:Base.Fn.id
  end

  module Seq = struct
    include Seq

    let map s ~f =
      fold s ~init:Base.Sequence.empty ~f:(fun acc x ->
          f x >>| fun x -> Base.Sequence.(append acc @@ return x))

    let all = map ~f:Base.Fn.id
  end

  let map_list_err ?prefix l ~f = List.map l ~f:(Base.Fn.compose (lift_err ?prefix) f)
  let iter_list_err ?prefix l ~f = List.iter l ~f:(Base.Fn.compose (lift_err ?prefix) f)
  let map_seq_err ?prefix s ~f = Seq.map s ~f:(Base.Fn.compose (lift_err ?prefix) f)
  let iter_seq_err ?prefix s ~f = Seq.iter s ~f:(Base.Fn.compose (lift_err ?prefix) f)
end
