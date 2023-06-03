open Context.Syntax

let run fn =
  let*? ctx = Expression.init fn in
  let*? () = Expression.fill ctx in
  let* () = Expression.map ctx ~f:(fun _ e -> Expression.eval e) in
  let*? fn = Expression.reify_to_fn ctx fn in
  !!fn
