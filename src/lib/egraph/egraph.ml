(* Adapted from: https://github.com/verse-lab/ego *)

include Common

module Extractor = Extractor
module Scheduler = Scheduler

type 'a extractor = 'a Extractor.t
type scheduler = Scheduler.t

let add = Builder.add
let fixpoint = Rewrite.fixpoint
