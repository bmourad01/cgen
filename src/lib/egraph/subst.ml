open Core

type info = {
  const : Virtual.const option;
  intv  : Bv_interval.t option;
  typ   : Type.t option;
  id    : Id.t
}

type t = info String.Map.t

let find = Map.find

let const i = i.const
let intv i = i.intv
let typ i = i.typ
