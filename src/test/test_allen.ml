open Core
open OUnit2
open Cgen
open Allen_interval_algebra

type range = {
  lo : int;
  hi : int;
}

let (--) lo hi = {lo; hi}

module A = Make(struct
    type point = int
    type t = range
    let lo t = t.lo
    let hi t = t.hi
    include Int.Replace_polymorphic_compare
  end)

let printer = Format.asprintf "%a" pp

let test expect a b _ =
  let got = A.relate a b in
  assert_equal ~printer expect got;
  let expect' = converse expect in
  let got' = A.relate b a in
  assert_equal ~msg:"Converse" ~printer expect' got'

let suite =
  "Allen interval algebra" >::: [
    "before" >:: test Before (1--3) (5--7);
    "meets" >:: test Meets (1--3) (3--8);
    "overlaps" >:: test Overlaps (1--5) (3--8);
    "finished_by" >:: test Finished_by (1--10) (4--10);
    "contains" >:: test Contains (1--10) (3--7);
    "starts" >:: test Starts (1--3) (1--10);
    "equal" >:: test Equal (2--7) (2--7);
    "started_by" >:: test Started_by (1--10) (1--3);
    "during" >:: test During (4--6) (1--10);
    "finishes" >:: test Finishes (4--10) (1--10);
    "overlapped_by" >:: test Overlapped_by (5--10) (1--7);
    "met_by" >:: test Met_by (10--15) (5--10);
    "after" >:: test After (10--15) (1--7);
  ]

let () = run_test_tt_main suite
