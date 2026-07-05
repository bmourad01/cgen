(** A minimal subset of BAP's [regular] library. *)

open Core

module type Printable = sig
  type t
  val to_string : t -> string
  val str : unit -> t -> string
  val pps : unit -> t -> string
  val ppo : Out_channel.t -> t -> unit
  val pp_seq : Format.formatter -> t Sequence.t -> unit
  include Pretty_printer.S with type t := t
end

module type S = sig
  type t [@@deriving bin_io, sexp, compare]
  include Printable            with type t := t
  include Comparable.S_binable with type t := t
  include Hashable.S_binable   with type t := t
end

module Printable(M : sig
    type t
    val pp : Format.formatter -> t -> unit
  end) : Printable with type t := M.t = struct
  let pp = M.pp
  let to_string t = Format.asprintf "%a" pp t
  let pps () t = to_string t
  let str = pps
  let ppo out x =
    let f = Format.formatter_of_out_channel out in
    pp f x;
    Format.pp_print_flush f ()
  let pp_seq ppf xs =
    Sequence.iter xs ~f:(fun x -> Format.fprintf ppf "%a@;" pp x)
end

module Make(M : sig
    type t [@@deriving bin_io, compare, sexp]
    val pp : Format.formatter -> t -> unit
    val hash : t -> int
  end) : S with type t := M.t = struct
  include M
  include Comparable.Make_binable(M)
  include Hashable.Make_binable_and_derive_hash_fold_t(M)
  include Printable(struct
      type t = M.t
      let pp = M.pp
    end)
end
