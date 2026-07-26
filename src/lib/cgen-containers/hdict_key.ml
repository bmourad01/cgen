open Core
open Hdict_key_intf

module Make(Name : Name) : S with type name := Name.t = struct
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

  let same (type a b) (x : a t) (y : b t) : (a, b) Type_equal.t =
    if equal x y then
      let module X = (val x.key : Witness with type t = a) in
      let module Y = (val y.key : Witness with type t = b) in
      match X.Id with
      | Y.Id -> Type_equal.T
      | _ -> failwith "Dict.Key.same: broken type equality"
    else failwith "Dict.Key.same: keys are not equal"
end
