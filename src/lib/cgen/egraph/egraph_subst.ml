module M = Matcher.Subst
module Id = Egraph_id

type info = {
  const : Virtual.const option;
  typ   : Type.t option;
  id    : Id.t;
}

type t = info M.t

let find = M.find
let const i = i.const
let typeof i = i.typ
