(* Efficient state + error monad. *)

open Core
open Monads.Std

module type S = sig
  type state

  val fail : string -> Error.t
end

module Make(M : S) = struct
  type 'a m = {
    run : 'r. reject:(Error.t -> 'r) -> accept:('a -> M.state -> 'r) -> M.state -> 'r;
  }

  let fail err = {
    run = fun ~reject ~accept:_ _ ->
      Error.to_string_hum err |> M.fail |> reject
  }

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

  let lift_err : 'a Or_error.t -> 'a m = function
    | Error err -> fail err
    | Ok x -> return x

  module Syntax = struct
    include SM.Syntax
    include SM.Let

    let (>>?) x f = lift_err x >>= f
    let (let*?) x f = x >>? f
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

  let lift_err : 'a Or_error.t -> 'a m = function
    | Error err -> fail err
    | Ok x -> return x
end
