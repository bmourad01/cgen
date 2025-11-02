open Core
open Virtual

include Egraph_common

module Rule = Egraph_rule
module Subst = Egraph_subst
module Builder = Egraph_builder

type rule = Rule.t

let init input depth_limit match_limit rules = {
  input;
  classes = Uf.create ();
  memo = Hashtbl.create (module Enode);
  node = Vec.create ();
  typs = Vec.create ();
  lmoved = Label.Table.create ();
  imoved = Vec.create ();
  pinned = Z.zero;
  ilbl = Vec.create ();
  lval = Label.Table.create ();
  depth_limit;
  match_limit;
  rules;
}

let check_ssa fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    Ok ()
  else
    Input.E.failf "Expected SSA form for function %s"
      (Func.name fn) ()

let run ?(depth_limit = 6) ?(match_limit = 20) fn tenv rules =
  let open Context.Syntax in
  let*? () = check_ssa fn in
  let*? input = Input.init fn tenv in
  let t = init input depth_limit match_limit rules in
  let*? () = Builder.run t in
  let ex = Extractor.init t in
  Extractor.cfg ex
