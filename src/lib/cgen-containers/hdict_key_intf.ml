(** The interface for {!Hdict} keys. *)

open Core

(** A unique identifier. *)
type uid = int

(** A human-readable name for a key. *)
module type Name = sig
  type t
  val to_string : t -> string
end

module type S = sig
  type 'a t
  type name

  (** Create a fresh key. *)
  val create : name:name -> ('a -> Sexp.t) -> 'a t

  (** Get the unique identifier of the key. *)
  val uid : 'a t -> uid

  (** Get the human-readable name of the key. *)
  val name : 'a t -> name

  (** Serialize the key. *)
  val to_sexp : 'a t -> 'a -> Sexp.t

  val compare : 'a t -> 'b t -> int
  val equal : 'a t -> 'b t -> bool

  (** Prove, at runtime, that two keys index the same type.

      Raises [Failure] if the keys are not equal.
  *)
  val same : 'a t -> 'b t -> ('a, 'b) Type_equal.t
end
