open Core
open Monads.Std
open Regular.Std

type state = {
  target    : Target.t;
  nextvar   : Int63.t;
  nextlabel : Int63.t;
} [@@deriving bin_io, compare, equal, hash, sexp]

module State = struct
  module T = struct
    type t = state [@@deriving bin_io, compare, equal, hash, sexp]
  end

  include T  

  include Regular.Make(struct
      include T

      let pp ppf s = Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_state s
      let version = "0.1"
      let module_name = Some "Cgen.Context.State"
    end)
end

type 'a t = {
  run : 'r. reject:(Error.t -> 'r) -> accept:('a -> state -> 'r) -> state -> 'r;
}

let fail err = {
  run = fun ~reject ~accept:_ _ ->
    Error.to_string_hum err |>
    Error.createf "Context error: %s" |>
    reject
}

module M = Monad.Make(struct
    type nonrec 'a t = 'a t

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

include M

let lift_err : 'a Or_error.t -> 'a t = function
  | Error err -> fail err
  | Ok x -> !!x

module Syntax = struct
  include M.Syntax
  include M.Let

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

let lift_err : 'a Or_error.t -> 'a t = function
  | Error err -> fail err
  | Ok x -> !!x

let target = gets @@ fun s -> s.target

type var = Var.t

module Var = struct
  let fresh typ =
    let* s = get () in
    let id = s.nextvar in
    let+ () = put {s with nextvar = Int63.succ id} in
    Var.temp (Obj.magic id : Var.id) typ
end

type label = Label.t

module Label = struct
  let init = Int63.(succ (Obj.magic Label.pseudoexit : Int63.t))

  let fresh =
    let* s = get () in
    let l = s.nextlabel in
    let+ () = put {s with nextlabel = Int63.succ l} in
    (Obj.magic l : Label.t)
end

module Virtual = struct
  let phi p =
    let+ label = Label.fresh in
    Virtual.Insn.phi p ~label

  let data d =
    let+ label = Label.fresh in
    Virtual.Insn.data d ~label

  let ctrl c =
    let+ label = Label.fresh in
    Virtual.Insn.ctrl c ~label

  let blk ?(phi = []) ?(data = []) ~ctrl () =
    let+ label = Label.fresh in
    Virtual.Blk.create ~phi ~data ~ctrl ~label ()

  let blk' ?(label = None) ?phi:(p = []) ?data:(d = []) ~ctrl:c () =
    let* phi = List.map p ~f:phi in
    let* data = List.map d ~f:data in
    let* ctrl = ctrl c in
    let+ label = match label with
      | None -> Label.fresh
      | Some l -> !!l in
    Virtual.Blk.create ~phi ~data ~ctrl ~label ()
end

let init target = {
  target;
  nextvar = Int63.zero;
  nextlabel = Label.init;
}

let reject err = Error err
let run x s = x.run s ~reject ~accept:(fun x s -> Ok (x, s))
let eval x s = x.run s ~reject ~accept:(fun x _ -> Ok x)
