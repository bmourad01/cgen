open Core
open OUnit2
open Cgen

let c1 : Type.compound = `compound ("c1", Some 4, [
    `elt (`i32, 4);
    `elt (`i8, 2);
  ])

let c1_layout : Type.layout = {
  align = 4;
  data = [
    `elt `i32;
    `elt `i32;
    `elt `i32;
    `elt `i32;
    `elt `i8;
    `elt `i8;
    `pad 2;
  ];
}

let c2 : Type.compound = `compound ("c2", None, [
    `elt (`i32, 1);
    `name "c1";
    `elt (`i16, 1);
  ])

let c2_layout : Type.layout = {
  align = 4;
  data = [
    `elt `i32;
    `elt `i32;
    `elt `i32;
    `elt `i32;
    `elt `i32;
    `elt `i8;
    `elt `i8;
    `pad 2;
    `elt `i16;
    `pad 2;
  ];
}

let gamma = function
  | "c1" -> c1_layout
  | "c2" -> c2_layout
  | s -> failwithf "gamma: %s is undefined" s ()

let sexp_of_layout l = Sexp.List (List.map l ~f:Type.sexp_of_datum)

let test_sizeof_compound (`compound (name, _, _) as t) ~expected =
  let l = Type.layout gamma t in
  let l_expected = gamma name in
  let layout_msg = Format.asprintf
      "expected layout %a, got %a"
      Type.pp_layout l_expected
      Type.pp_layout l in
  assert_bool layout_msg @@ Type.equal_layout l l_expected;
  let s = Type.sizeof_layout l in
  let size_msg = Format.asprintf
      "expected size %d in bits for type %a, got %d"
      expected Type.pp_compound t s in
  assert_bool size_msg (s = expected)

let test_c1 _ = test_sizeof_compound c1 ~expected:160
let test_c2 _ = test_sizeof_compound c2 ~expected:224

let suite = "Test types" >::: [
    "Test sizeof compound 1" >:: test_c1;
    "Test sizeof compound 2" >:: test_c2;
  ]

let () = run_test_tt_main suite
