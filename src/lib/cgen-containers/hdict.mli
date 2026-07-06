(** A type-safe, heterogeneous dictionary.

    It is an extensible collection of values paired with "keys" that witness
    their types. To preserve type safety, keys must be declared ahead of time.
*)

module type Name = Hdict_intf.Name

module Make(Name : Name) : sig
  module Key : Hdict_intf.Key
    with type name := Name.t
     and type uid := int

  include Hdict_intf.S with type 'a key = 'a Key.t
end
