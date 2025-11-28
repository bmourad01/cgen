open Core
open OUnit2
open Cgen

let c1 : Type.compound = `compound ("c1", Some 4, [
    `elt (`i32, 4);
    `elt (`i8, 2);
  ])

let c2 : Type.compound = `compound ("c2", None, [
    `elt (`i32, 1);
    `name ("c1", 1);
    `elt (`i16, 1);
  ])

let c3 : Type.compound = `compound ("c3", Some 4, [])

let c4 : Type.compound = `compound ("c4", None, [
    `name ("c3", 1);
    `elt (`i32, 1);
  ])

let c5 : Type.compound = `compound ("c5", None, [
    `name ("c3", 1);
    `elt (`i32, 1);
    `name ("c3", 1);
    `elt (`i32, 1);
  ])

let c6 : Type.compound = `compound ("c6", Some 8, [])

let c7 : Type.compound = `compound ("c7", None, [
    `name ("c6", 1);
    `elt (`i32, 1);
    `name ("c6", 1);
    `elt (`i32, 1);
  ])

let c8 : Type.compound = `compound ("c8", None, [])

let c9 : Type.compound = `compound ("c9", None, [
    `elt (`f32, 1);
    `elt (`i8, 1);
    `name ("c8", 1);
    `elt (`i8, 1);
    `name ("c8", 1);
    `elt (`i32, 1);
  ])

let c10 : Type.compound = `compound ("c10", None, [
    `name ("c1", 2);
  ])

let c11 : Type.compound = `compound ("c11", None, [
    `elt (`i16, 3);
    `elt (`i32, 1);
  ])

let c12 : Type.compound = `compound ("c12", Some 8, [
    `elt (`i32, 1);
  ])

let c13 : Type.compound = `compound ("c13", None, [
    `elt (`i8, 3);
  ])

let c14 : Type.compound = `compound ("c14", Some 8, [
    `elt (`i16, 1);
  ])

let c15 : Type.compound = `compound ("c15", Some 8, [
    `elt (`i8, 1);
    `elt (`i16, 1);
    `elt (`i32, 1);
    `elt (`i8, 1);
  ])

let opaque4 : Type.compound = `opaque ("opaque4", 4, 4)

let c16 : Type.compound = `compound ("c16", Some 4, [
    `name ("opaque4", 1);
    `name ("opaque4", 1);
  ])

let c1arr : Type.compound = `compound ("c1arr", None, [
    `name ("c1", 3);
  ])

let sexp = Fn.compose Type.Layout.t_of_sexp Sexp.of_string

let l1 = sexp "((align 4) (data (i32 i32 i32 i32 i8 i8 (pad 2))))"
let l2 = sexp "((align 4) (data (i32 i32 i32 i32 i32 i8 i8 (pad 2) i16 (pad 2))))"
let l3 = sexp "((align 4) (data ()))"
let l4 = sexp "((align 4) (data (i32)))"
let l5 = sexp "((align 4) (data (i32 i32)))"
let l6 = sexp "((align 8) (data ()))"
let l7 = sexp "((align 8) (data (i32 (pad 4) i32 (pad 4))))"
let l8 = sexp "((align 1) (data ()))"
let l9 = sexp "((align 4) (data (f32 i8 i8 (pad 2) i32)))"
let l10 = sexp "((align 4) (data (i32 i32 i32 i32 i8 i8 (pad 2) i32 i32 i32 i32 i8 i8 (pad 2))))"
let l11 = sexp "((align 4) (data (i16 i16 i16 (pad 2) i32)))"
let l12 = sexp "((align 8) (data (i32 (pad 4))))"
let l13 = sexp "((align 1) (data (i8 i8 i8)))"
let l14 = sexp "((align 8) (data (i16 (pad 6))))"
let l15 = sexp "((align 8) (data (i8 (pad 1) i16 i32 i8 (pad 7))))"
let lopaque4 = sexp "((align 4) (data ((opaque 4))))"
let l16 = sexp "((align 4) (data ((opaque 8))))"
let l1arr = sexp "((align 4) (data (i32 i32 i32 i32 i8 i8 (pad 2) i32 i32 i32 i32 i8 i8 (pad 2) i32 i32 i32 i32 i8 i8 (pad 2))))"

let gamma = function
  | "c1" -> l1
  | "c2" -> l2
  | "c3" -> l3
  | "c4" -> l4
  | "c5" -> l5
  | "c6" -> l6
  | "c7" -> l7
  | "c8" -> l8
  | "c9" -> l9
  | "c10" -> l10
  | "c11" -> l11
  | "c12" -> l12
  | "c13" -> l13
  | "c14" -> l14
  | "c15" -> l15
  | "opaque4" -> lopaque4
  | "c16" -> l16
  | "c1arr" -> l1arr
  | s -> failwithf "gamma: %s is undefined" s ()

let _sexp_of_layout l = Sexp.List (List.map l ~f:Type.sexp_of_datum)

let test_sizeof_compound (t : Type.compound) ~expected =
  let l = Type.layout_exn gamma t in
  let name = Type.compound_name t in
  let l_expected = gamma name in
  let layout_msg = Format.asprintf
      "expected layout %a, got %a"
      Type.pp_layout l_expected
      Type.pp_layout l in
  assert_bool layout_msg @@ Type.equal_layout l l_expected;
  let s = Type.sizeof_layout l in
  let size_msg = Format.asprintf
      "expected size %d in bytes for type %a, got %d"
      expected Type.pp_compound t s in
  assert_bool size_msg (s = expected)

let test_c1 _ = test_sizeof_compound c1 ~expected:20
let test_c2 _ = test_sizeof_compound c2 ~expected:28
let test_c3 _ = test_sizeof_compound c3 ~expected:0
let test_c4 _ = test_sizeof_compound c4 ~expected:4
let test_c5 _ = test_sizeof_compound c5 ~expected:8
let test_c6 _ = test_sizeof_compound c6 ~expected:0
let test_c7 _ = test_sizeof_compound c7 ~expected:16
let test_c8 _ = test_sizeof_compound c8 ~expected:0
let test_c9 _ = test_sizeof_compound c9 ~expected:12
let test_c10 _ = test_sizeof_compound c10 ~expected:40
let test_c11 _ = test_sizeof_compound c11 ~expected:12
let test_c12 _ = test_sizeof_compound c12 ~expected:8
let test_c13 _ = test_sizeof_compound c13 ~expected:3
let test_c14 _ = test_sizeof_compound c14 ~expected:8
let test_c15 _ = test_sizeof_compound c15 ~expected:16
let test_opaque4 _ = test_sizeof_compound opaque4 ~expected:4
let test_c16 _ = test_sizeof_compound c16 ~expected:8
let test_c1arr _ = test_sizeof_compound c1arr ~expected:60

let suite = "Test types" >::: [
    "Test sizeof compound 1" >:: test_c1;
    "Test sizeof compound 2" >:: test_c2;
    "Test sizeof compound 3" >:: test_c3;
    "Test sizeof compound 4" >:: test_c4;
    "Test sizeof compound 5" >:: test_c5;
    "Test sizeof compound 6" >:: test_c6;
    "Test sizeof compound 7" >:: test_c7;
    "Test sizeof compound 8" >:: test_c8;
    "Test sizeof compound 9" >:: test_c9;
    "Test sizeof compound 10" >:: test_c10;
    "Test sizeof compound 11" >:: test_c11;
    "Test sizeof compound 12" >:: test_c12;
    "Test sizeof compound 13" >:: test_c13;
    "Test sizeof compound 14" >:: test_c14;
    "Test sizeof compound 15" >:: test_c15;
    "Test sizeof compound opaque4" >:: test_opaque4;
    "Test sizeof compound 16" >:: test_c16;
    "Test sizeof compound 1 (array)" >:: test_c1arr;
  ]

let () = run_test_tt_main suite
