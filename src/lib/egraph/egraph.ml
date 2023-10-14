open Core
open Virtual

include Common

module Rule = Rule
module Subst = Subst

type rule = Rule.t

let init input fuel = {
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
  intv = Id.Table.create ();
  fuel;
}

let check_ssa fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    Ok ()
  else
    Input.E.failf "Expected SSA form for function %s"
      (Func.name fn) ()

let run ?(fuel = 5) fn tenv rules =
  let open Context.Syntax in
  let*? () = check_ssa fn in
  let*? input = Input.init fn tenv in
  let t = init input fuel in
  let*? () = Builder.run t rules in
  let ex = Extractor.init t in
  Extractor.cfg ex
