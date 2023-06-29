(* Adapted from: https://github.com/verse-lab/ego *)

open Core

include Common

module Extractor = Extractor
module Scheduler = Scheduler

type extractor = Extractor.t
type scheduler = Scheduler.t

let fixpoint = Rewrite.fixpoint

let init input = {
  input;
  uf = Uf.create ();
  nodes = Hashtbl.create (module Enode);
  classes = Id.Table.create ();
  pending = Vec.create ();
  analyses = Vec.create ();
  provenance = {
    src = Id.Table.create ();
    dst = Label.Table.create ();
  };
  ver = 0;
}

let create fn =
  let open Input.E.Let in
  let+ input, exp = Input.create fn in
  let t = init input in
  Hashtbl.iteri exp ~f:(fun ~key:l ~data:e ->
      let id = Parser.exp t e in
      Hashtbl.set t.provenance.dst ~key:l ~data:id;
      update_provenance t id l);
  (* Propagate constants immediately. *)
  Rewrite.rebuild t;
  t
