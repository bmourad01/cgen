open Core

include Common

module Rule = Rule
module Extractor = Extractor

type extractor = Extractor.t
type rule = Rule.t

let init input fuel = {
  input;
  classes = Uf.create ();
  memo = Hashtbl.create (module Enode);
  node = Vec.create ();
  id2lbl = Id.Table.create ();
  lbl2id = Label.Table.create ();
  fuel;
}

let create ?(fuel = 1000) fn tenv rules =
  let open Input.E.Let in
  let* input = Input.init fn in
  let t = init input fuel in
  let+ () = Builder.run t tenv rules in
  t
