open Core
open Virtual

include Common

module Rule = Rule
module Subst = Subst

type rule = Rule.t

let init input depth_limit match_limit rules = {
  input;
  classes = Uf.create ();
  memo = Hashtbl.create (module Enode);
  node = Vec.create ();
  lmoved = Label.Table.create ();
  imoved = Id.Table.create ();
  imoved2 = Id.Table.create ();
  licm = Id.Hash_set.create ();
  id2lbl = Id.Table.create ();
  lbl2id = Label.Table.create ();
  typs = Id.Table.create ();
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
