open Core

type info = {
  const : Virtual.const option;
  typ   : Type.t option;
  id    : Id.t
}

type t = info String.Map.t

let find = Map.find
let const i = i.const
let typeof i = i.typ
