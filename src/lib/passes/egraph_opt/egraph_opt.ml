(* TODO: add user-configurable options for disabling certain
   groups of rules. *)

module Rules = Egraph_opt_rules

let run tenv fn = Egraph.run fn tenv Rules.all
