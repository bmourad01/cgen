(** Type-safe keys for {!Hdict}, adapted from BAP's Knowledge Base.

    Each key carries a fresh extensible-variant "witness" constructor
    that lets two keys prove, at run time, that they index the same type.

    Keys are ordered by a monotonically increasing [uid].
*)

open Core

type uid = int

module type Name = sig
  type t
  val to_string : t -> string
end

module Make(Name : Name) = struct
  let last_id = ref (0 : uid)

  type 'a witness = ..

  module type Witness = sig
    type t
    type _ witness += Id : t witness
  end

  type 'a typeid = (module Witness with type t = 'a)

  type 'a t = {
    ord  : uid;
    key  : 'a typeid;
    name : Name.t;
    show : 'a -> Sexp.t;
  }

  let newtype (type a) () : a typeid =
    let module Type = struct
      type t = a
      type _ witness += Id : t witness
    end in
    (module Type)

  let create ~name show =
    let key = newtype () in
    Int.incr last_id;
    {key; ord = !last_id; name; show}

  let uid t = t.ord [@@inline]
  let name t = t.name [@@inline]
  let to_sexp t = t.show [@@inline]
  let compare x y = Int.compare (uid x) (uid y) [@@inline]
  let equal x y = Int.equal (uid x) (uid y) [@@inline]

  (* Prove that two equal keys index the same type. *)
  let same (type a b) (x : a t) (y : b t) : (a, b) Type_equal.t =
    if equal x y then
      let module X = (val x.key : Witness with type t = a) in
      let module Y = (val y.key : Witness with type t = b) in
      match X.Id with
      | Y.Id -> Type_equal.T
      | _ -> failwith "Dict.Key.same: broken type equality"
    else failwith "Dict.Key.same: keys are not equal"
end
