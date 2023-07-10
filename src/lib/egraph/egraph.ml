(* Adapted from: https://github.com/verse-lab/ego *)

open Core

include Common

module Extractor = Extractor
module Scheduler = Scheduler

type extractor = Extractor.t
type scheduler = Scheduler.t

let fixpoint = Rewrite.fixpoint

let init analyze input = {
  input;
  uf = Uf.create ();
  nodes = Hashtbl.create (module Enode);
  classes = Id.Table.create ();
  pending = Vec.create ();
  analyses = Vec.create ();
  id2lbl = Id.Table.create ();
  lbl2id = Label.Table.create ();
  analyze;
  ver = 0;
}

let create ?(analyze = true) fn =
  let open Input.E.Let in
  let* input = Input.init fn in
  let t = init analyze input in
  let+ () = Builder.run t in
  if analyze then Rewrite.rebuild t;
  t
