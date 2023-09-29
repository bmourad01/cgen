open Core
open OUnit2
open Cgen

module I = Bv_interval

let expect x i =
  let size = I.size_of i in
  let i' = match x with
    | `empty -> I.create_empty ~size
    | `full -> I.create_full ~size
    | `def (lo, hi) -> I.create ~lo ~hi ~size in
  let msg = Format.asprintf "Expected %a, got %a" I.pp i' I.pp i in
  assert_bool msg (I.equal i i')

let test_1 _ =
  let size = 32 in
  let module B = (val Bv.modular size) in
  let i1 = I.create ~lo:Bv.one ~hi:B.(int 5) ~size in
  let i2 = I.create ~lo:B.(int 3) ~hi:B.(int 7) ~size in
  expect (`def (B.int 1, B.int 7)) @@ I.union i1 i2;
  expect (`def (B.int 3, B.int 5)) @@ I.intersect i1 i2

let suite = "Test BV intervals" >::: [
    "Test 1" >:: test_1;
  ]

let () = run_test_tt_main suite
