(** A small monad library. *)

open Core

module type Basic = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : [`Define_using_bind | `Custom of ('a t -> f:('a -> 'b) -> 'b t)]
end

module Syntax = struct
  module type S = sig
    type 'a t
    val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
    val (>>|) : 'a t -> ('a -> 'b) -> 'b t
    val (>=>) : ('a -> 'b t) -> ('b -> 'c t) -> ('a -> 'c t)
    val (!!) : 'a -> 'a t
  end
  module Let = struct
    module type S = sig
      type 'a t
      val (let*) : 'a t -> ('a -> 'b t) -> 'b t
      val (and*) : 'a t -> 'b t -> ('a * 'b) t
      val (let+) : 'a t -> ('a -> 'b) -> 'b t
      val (and+) : 'a t -> 'b t -> ('a * 'b) t
    end
  end
end

(** Monadic combinators over a container ['a c]. *)
module type Collection = sig
  type 'a t
  type 'a c
  val all : 'a t c -> 'a c t
  val all_unit : unit t c -> unit t
  val map : 'a c -> f:('a -> 'b t) -> 'b c t
  val iter : 'a c -> f:('a -> unit t) -> unit t
  val fold : 'a c -> init:'b -> f:('b -> 'a -> 'b t) -> 'b t
  val fold_left : 'a c -> init:'b -> f:('b -> 'a -> 'b t) -> 'b t
  val fold_right : 'a c -> f:('a -> 'b -> 'b t) -> init:'b -> 'b t
  val exists : 'a c -> f:('a -> bool t) -> bool t
  val for_all : 'a c -> f:('a -> bool t) -> bool t
  val find : 'a c -> f:('a -> bool t) -> 'a option t
  val find_map : 'a c -> f:('a -> 'b option t) -> 'b option t
  val filter : 'a c -> f:('a -> bool t) -> 'a c t
  val filter_map : 'a c -> f:('a -> 'b option t) -> 'b c t
  val reduce : 'a c -> f:('a -> 'a -> 'a t) -> 'a option t
end

module type S = sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map : 'a t -> f:('a -> 'b) -> 'b t
  val join : 'a t t -> 'a t
  val ignore_m : 'a t -> unit t
  val void : 'a t -> unit t
  val all : 'a t list -> 'a list t
  val all_unit : unit t list -> unit t
  val sequence : unit t list -> unit t

  include Syntax.S with type 'a t := 'a t
  include Syntax.Let.S with type 'a t := 'a t

  module Let : Syntax.Let.S with type 'a t := 'a t
  module Syntax : Syntax.S with type 'a t := 'a t
  module List : Collection with type 'a t := 'a t and type 'a c := 'a list
  module Seq : Collection with type 'a t := 'a t and type 'a c := 'a Sequence.t
end

module Make(M : Basic) : S with type 'a t := 'a M.t = struct
  type 'a t = 'a M.t [@@ocaml.warning "-34"]

  let return = M.return
  let bind = M.bind
  let (>>=) = M.bind

  let map = match M.map with
    | `Custom f -> f
    | `Define_using_bind -> fun m ~f -> bind m (fun x -> return (f x))

  let (>>|) m f = map m ~f
  let (>=>) g h x = g x >>= h
  let (!!) = return

  let join m = m >>= Fn.id
  let ignore_m m = map m ~f:ignore
  let void = ignore_m

  module Syntax = struct
    let (>>=) = (>>=)
    let (>>|) = (>>|)
    let (>=>) = (>=>)
    let (!!) = (!!)
  end

  module Let = struct
    let (let*) = (>>=)
    let (let+) m f = map m ~f
    let (and+) a b = a >>= fun a -> b >>| fun b -> (a, b)
    let (and*) = (and+)
  end

  include Let

  module Collect(C : sig
      type 'a t
      val fold : 'a t -> init:'b -> f:('b -> 'a -> 'b) -> 'b
      val fold_right : 'a t -> init:'b -> f:('a -> 'b -> 'b) -> 'b
      val of_list : 'a list -> 'a t
    end) = struct
    type nonrec 'a t = 'a M.t [@@ocaml.warning "-34"]
    type 'a c = 'a C.t [@@ocaml.warning "-34"]

    let fold xs ~init ~f =
      C.fold xs ~init:(return init) ~f:(fun acc x -> acc >>= fun a -> f a x)

    let fold_left = fold

    let fold_right xs ~f ~init =
      C.fold_right xs ~init:(return init) ~f:(fun x acc -> acc >>= fun a -> f x a)

    let iter xs ~f = fold xs ~init:() ~f:(fun () x -> f x)
    let to_list xs = C.fold xs ~init:[] ~f:(fun acc x -> x :: acc) |> List.rev

    let map xs ~f =
      let rec aux items k = match items with
        | [] -> k []
        | x :: xs -> f x >>= fun y -> aux xs (fun ys -> k (y :: ys)) in
      aux (to_list xs) (fun ys -> return (C.of_list ys))

    let filter_map xs ~f =
      let rec aux items k = match items with
        | [] -> k []
        | x :: xs -> f x >>= (function
            | None -> aux xs k
            | Some y -> aux xs (fun ys -> k (y :: ys))) in
      aux (to_list xs) (fun ys -> return (C.of_list ys))

    let filter xs ~f =
      filter_map xs ~f:(fun x -> f x >>| fun b -> if b then Some x else None)

    let all xs = map xs ~f:Fn.id
    let all_unit xs = iter xs ~f:Fn.id

    let find_map xs ~f =
      let rec go = function
        | [] -> return None
        | x :: xs -> f x >>= (function None -> go xs | some -> return some) in
      go (to_list xs)

    let find xs ~f =
      find_map xs ~f:(fun x -> f x >>| fun b -> if b then Some x else None)

    let exists xs ~f = find xs ~f >>| Option.is_some
    let for_all xs ~f = find xs ~f:(fun x -> f x >>| not) >>| Option.is_none

    let reduce xs ~f = match to_list xs with
      | [] -> return None
      | x :: xs -> fold (C.of_list xs) ~init:x ~f >>| Option.some
  end

  module List = Collect(struct
      type 'a t = 'a list
      let fold = List.fold
      let fold_right xs ~init ~f = List.fold_right xs ~init ~f
      let of_list = Fn.id
    end)

  module Seq = Collect(struct
      type 'a t = 'a Sequence.t
      let fold = Sequence.fold
      let fold_right xs ~init ~f =
        Base.List.fold_right (Sequence.to_list xs) ~init ~f
      let of_list = Sequence.of_list
    end)

  let all = List.all
  let all_unit = List.all_unit
  let sequence = List.all_unit
end

module Option = struct
  type 'a t = 'a option

  include (Make(struct
             type nonrec 'a t = 'a t
             let return x = Some x
             let bind m f = match m with Some x -> f x | None -> None
             let map = `Custom (fun m ~f ->
                 match m with Some x -> Some (f x) | None -> None)
           end) : S with type 'a t := 'a t)

  let guard b = if b then Some () else None
  let on b m = if b then m else Some ()
  let unless b m = if b then Some () else m
end

module Error = struct
  type 'a t = 'a Or_error.t

  include (Make(struct
             type nonrec 'a t = 'a t
             let return x = Ok x
             let bind m f = match m with Ok x -> f x | Error _ as e -> e
             let map = `Custom (fun m ~f ->
                 match m with Ok x -> Ok (f x) | Error _ as e -> e)
           end) : S with type 'a t := 'a t)

  let fail e = Error e
  let catch m f = match m with Ok _ as x -> x | Error e -> f e
  let failf fmt = Format.kasprintf (fun msg () -> Error (Error.of_string msg)) fmt
end

(** An efficient state + error monad.

    The monadic type is a single CPS function that takes a state plus [reject]
    and [accept] continuations, avoiding any per-bind allocation of [Result.t]
    cells.

    Parameterized over the user's [error] type via [S.of_or_error].
*)
module Sm = struct
  module Error = Core.Error

  module type S = sig
    type state
    type error

    (** Lift an [Error.t] (used by [failf] and [lift_err]) into the user's
        error type. *)
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

    module SM = Make(struct
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

    let map_list_err ?prefix l ~f =
      List.map l ~f:(Base.Fn.compose (lift_err ?prefix) f)

    let iter_list_err ?prefix l ~f =
      List.iter l ~f:(Base.Fn.compose (lift_err ?prefix) f)

    let map_seq_err ?prefix s ~f =
      Seq.map s ~f:(Base.Fn.compose (lift_err ?prefix) f)

    let iter_seq_err ?prefix s ~f =
      Seq.iter s ~f:(Base.Fn.compose (lift_err ?prefix) f)
  end
end
