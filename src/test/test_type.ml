open Core
open OUnit2
open Cgen

let c1 : Type.compound = `compound ("c1", Some 4, [
    `elt (`i32, 4);
    `elt (`i8, 1);
  ])

let c2 : Type.compound = `compound ("c2", None, [
    `elt (`i32, 1);
    `name "c1";
    `elt (`i16, 1);
  ])

let gamma = function
  | "c1" -> List.init 5 ~f:(fun _ -> `i32)
  | s -> failwithf "gamma: %s is undefined" s ()

let test_sizeof_compound t ~expected =
  let s = Type.sizeof_compound gamma t in
  let msg = Format.asprintf
      "expected size %d in bits for type %a, got %d"
      expected Type.pp_compound t s in
  assert_bool msg (s = expected)

let test_c1 _ = test_sizeof_compound c1 ~expected:160
let test_c2 _ = test_sizeof_compound c2 ~expected:224

let suite = "Test types" >::: [
    "Test sizeof compound 1" >:: test_c1;
    "Test sizeof compound 2" >:: test_c2;
  ]

let () = run_test_tt_main suite
