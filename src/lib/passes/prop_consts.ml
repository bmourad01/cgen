open Core
open Monads.Std
open Regular.Std
open Virtual

module E = Monad.Result.Error

open E.Let

let run fn =
  let* ctx = Expression.init fn in
  let* () = Expression.fill ctx in
  Expression.map ctx ~f:(fun _ e -> Expression.eval e);
  Expression.reify_to_fn ctx fn
