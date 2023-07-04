open Core
open Context.Syntax

let rules =
  let open Egraph.Enode in
  let open Egraph.Rule in
  let x = var "x" in
  let y = var "y" in [
    (* Unconditional branch. *)
    (Obr & [exp (Obool  true); x; y]) => (Ojmp & [x]);
    (Obr & [exp (Obool false); x; y]) => (Ojmp & [y]);
    (* Branch to same destination. *)
    (Obr & [x; y; y]) => (Ojmp & [y]);
    (* Copy propagation. *)
    (Ounop (`copy  `i8) & [x]) => x;
    (Ounop (`copy `i16) & [x]) => x;
    (Ounop (`copy `i32) & [x]) => x;
    (Ounop (`copy `i64) & [x]) => x;
  ]  

let cost ~child n =
  let init = match Egraph.Enode.op n with
    | Obool _ | Odouble _ | Oint _ | Osingle _ | Osym _ -> 0
    | Ovar _ -> 1
    | _ -> 2 in
  Egraph.Enode.children n |>
  List.fold ~init ~f:(fun k c -> k + child c)

let run fn =
  let*? eg = Egraph.create fn in
  let _ = Egraph.fixpoint eg rules in
  let ex = Egraph.Extractor.init eg ~cost in
  Egraph.Extractor.reify ex
