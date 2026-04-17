open Core
open Cgen

let sexp = Fn.compose Type.Layout.t_of_sexp Sexp.of_string

(* Struct types *)

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

let c17 : Type.compound = `compound ("c17", None, [
    `name ("u1", 1);
    `elt (`i32, 1);
  ])

let l1 = sexp "((align 4) (size 20) (members (First (i32 i32 i32 i32 i8 i8 (pad 2)))))"
let l2 = sexp "((align 4) (size 28) (members (First (i32 i32 i32 i32 i32 i8 i8 (pad 2) i16 (pad 2)))))"
let l3 = sexp "((align 4) (size 0) (members (First ())))"
let l4 = sexp "((align 4) (size 4) (members (First (i32))))"
let l5 = sexp "((align 4) (size 8) (members (First (i32 i32))))"
let l6 = sexp "((align 8) (size 0) (members (First ())))"
let l7 = sexp "((align 8) (size 16) (members (First (i32 (pad 4) i32 (pad 4)))))"
let l8 = sexp "((align 1) (size 0) (members (First ())))"
let l9 = sexp "((align 4) (size 12) (members (First (f32 i8 i8 (pad 2) i32))))"
let l10 = sexp "((align 4) (size 40) (members (First (i32 i32 i32 i32 i8 i8 (pad 2) i32 i32 i32 i32 i8 i8 (pad 2)))))"
let l11 = sexp "((align 4) (size 12) (members (First (i16 i16 i16 (pad 2) i32))))"
let l12 = sexp "((align 8) (size 8) (members (First (i32 (pad 4)))))"
let l13 = sexp "((align 1) (size 3) (members (First (i8 i8 i8))))"
let l14 = sexp "((align 8) (size 8) (members (First (i16 (pad 6)))))"
let l15 = sexp "((align 8) (size 16) (members (First (i8 (pad 1) i16 i32 i8 (pad 7)))))"
let lopaque4 = sexp "((align 4) (size 4) (members (First ((opaque 4)))))"
let l16 = sexp "((align 4) (size 8) (members (First ((opaque 8)))))"
let l1arr = sexp "((align 4) (size 60) (members (First (i32 i32 i32 i32 i8 i8 (pad 2) i32 i32 i32 i32 i8 i8 (pad 2) i32 i32 i32 i32 i8 i8 (pad 2)))))"
let l17 = sexp "((align 4) (size 8) (members (First ((union (u1 4)) i32))))"

(* Union types *)

let u1 : Type.compound = `union ("u1", None, [
    `elt (`f32, 1);
    `elt (`i32, 1);
  ])

let u2 : Type.compound = `union ("u2", None, [
    `elt (`f64, 1);
    `elt (`i32, 1);
  ])

let u3 : Type.compound = `union ("u3", None, [
    `elt (`f32, 1);
    `elt (`f64, 1);
  ])

let u4 : Type.compound = `union ("u4", None, [
    `elt (`i8, 8);
    `elt (`f64, 1);
  ])

let u5 : Type.compound = `union ("u5", None, [
    `elt (`i64, 1);
  ])

let u6 : Type.compound = `union ("u6", None, [])

let u7 : Type.compound = `union ("u7", None, [
    `name ("c1", 1);
    `elt (`f64, 1);
  ])

let u8 : Type.compound = `union ("u8", Some 16, [
    `elt (`i32, 1);
    `elt (`f32, 1);
  ])

let u9 : Type.compound = `union ("u9", None, [
    `elt (`i16, 1);
    `elt (`i8, 1);
  ])

let lu1 = sexp "((align 4) (size 4) (members (Second ((f32) (i32)))))"
let lu2 = sexp "((align 8) (size 8) (members (Second ((f64) (i32 (pad 4))))))"
let lu3 = sexp "((align 8) (size 8) (members (Second ((f32 (pad 4)) (f64)))))"
let lu4 = sexp "((align 8) (size 8) (members (Second ((i8 i8 i8 i8 i8 i8 i8 i8) (f64)))))"
let lu5 = sexp "((align 8) (size 8) (members (Second ((i64)))))"
let lu6 = sexp "((align 1) (size 0) (members (Second ())))"
let lu7 = sexp "((align 8) (size 24) (members (Second ((i32 i32 i32 i32 i8 i8 (pad 6)) (f64 (pad 16))))))"
let lu8 = sexp "((align 16) (size 16) (members (Second ((i32 (pad 12)) (f32 (pad 12))))))"
let lu9 = sexp "((align 2) (size 2) (members (Second ((i16) (i8 (pad 1))))))"

(* The tests *)

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
  | "c17" -> l17
  | "u1" -> lu1
  | "u2" -> lu2
  | "u3" -> lu3
  | "u4" -> lu4
  | "u5" -> lu5
  | "u6" -> lu6
  | "u7" -> lu7
  | "u8" -> lu8
  | "u9" -> lu9
  | s -> failwithf "gamma: %s is undefined" s ()

let test_layout (t : Type.compound) =
  let l = Type.layout_exn gamma t in
  let name = Type.compound_name t in
  let expected = gamma name in
  if not (Type.equal_layout l expected) then
    failwithf "expected layout %s, got %s"
      (Format.asprintf "%a" Type.pp_layout expected)
      (Format.asprintf "%a" Type.pp_layout l)
      ()

let%test_unit "layout c1"      = test_layout c1
let%test_unit "layout c2"      = test_layout c2
let%test_unit "layout c3"      = test_layout c3
let%test_unit "layout c4"      = test_layout c4
let%test_unit "layout c5"      = test_layout c5
let%test_unit "layout c6"      = test_layout c6
let%test_unit "layout c7"      = test_layout c7
let%test_unit "layout c8"      = test_layout c8
let%test_unit "layout c9"      = test_layout c9
let%test_unit "layout c10"     = test_layout c10
let%test_unit "layout c11"     = test_layout c11
let%test_unit "layout c12"     = test_layout c12
let%test_unit "layout c13"     = test_layout c13
let%test_unit "layout c14"     = test_layout c14
let%test_unit "layout c15"     = test_layout c15
let%test_unit "layout opaque4" = test_layout opaque4
let%test_unit "layout c16"     = test_layout c16
let%test_unit "layout c1arr"   = test_layout c1arr
let%test_unit "layout c17"     = test_layout c17
let%test_unit "layout u1"      = test_layout u1
let%test_unit "layout u2"      = test_layout u2
let%test_unit "layout u3"      = test_layout u3
let%test_unit "layout u4"      = test_layout u4
let%test_unit "layout u5"      = test_layout u5
let%test_unit "layout u6"      = test_layout u6
let%test_unit "layout u7"      = test_layout u7
let%test_unit "layout u8"      = test_layout u8
let%test_unit "layout u9"      = test_layout u9
