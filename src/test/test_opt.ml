open Core
open OUnit2
open Cgen

module Test_target = struct
  let r0 = Target.Reg.r64 "r0"
  let r1 = Target.Reg.r64 "r1"
  let r2 = Target.Reg.r64 "r2"
  let r3 = Target.Reg.r64 "r3"

  let d0 = Target.Reg.r64 "d0"
  let d1 = Target.Reg.r64 "d1"
  let d2 = Target.Reg.r64 "d2"
  let d3 = Target.Reg.r64 "d3"

  let sp = Target.Reg.r64 "sp"

  let cf = Target.Reg.r1 "cf"
  let sf = Target.Reg.r1 "sf"
  let zf = Target.Reg.r1 "zf"
  let vf = Target.Reg.r1 "vf"

  let t = Target.create ()
      ~name:"test"
      ~word:`i64
      ~little:true
      ~flag:[cf; sf; zf; vf]
      ~fp:[d0; d1; d2; d3]
      ~gpr:[r0; r1; r2; r3]
      ~sp
end

(* Ignore certain characters when comparing the output *)
let fmt = String.filter ~f:(function
    | '\r' | '\n' | '\t' | ' ' -> false
    | _ -> true)

let (=>) p expected =
  Context.init Test_target.t |>
  Context.eval begin
    let open Context.Syntax in
    let* target = Context.target in
    let* m = Parse.Virtual.from_string p in
    let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
    let*? tenv = Typecheck.run m ~target in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Ssa.run in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Simplify_cfg.run in
    let m = Virtual.Module.map_funs m ~f:Passes.Tailcall.run in
    let* m = Context.Virtual.Module.map_funs m ~f:(Passes.Peephole.run tenv) in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
    let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Simplify_cfg.run in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
    !!(Format.asprintf "%a" Virtual.Module.pp m)
  end |> function
  | Error err ->
    assert_failure @@ Format.asprintf "%a" Error.pp err
  | Ok p' ->
    let msg = Format.asprintf "Expected:@,@[%s@]@,Got:@,@[%s@]" expected p' in
    assert_equal (fmt p') (fmt expected) ~msg ~cmp:String.equal

let test_mul_by_1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = mul.w %x, 1_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     ret %x
   }"

let test_mul_by_2 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = mul.w %x, 2_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = lsl.w %x, 0x1_w ; @2
     ret %0
   }"

let test_mul_by_8 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = mul.w %x, 8_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = lsl.w %x, 0x3_w ; @2
     ret %0
   }"

let test_sdiv_by_1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = div.w %x, 1_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     ret %x
   }"

let test_sdiv_by_4 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = div.w %x, 4_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %2 = slt.w %x, 0x0_w ; @4
     %3 = add.w %x, 0x3_w ; @5
     %1 = sel.w %2, %3, %x ; @3
     %0 = asr.w %1, 0x2_w ; @2
     ret %0
   }"

let test_sdiv_by_11 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = div.w %x, 11_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = mulh.w %x, 0x1745d175_w ; @3
     %2 = lsr.w %1, 0x1f_w ; @4
     %0 = add.w %1, %2 ; @2
     ret %0
   }"

let test_udiv_by_8 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = udiv.w %x, 8_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = lsr.w %x, 0x3_w ; @2
     ret %0
   }"

let test_srem_by_2 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = rem.w %x, 2_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %3 = lsr.w %x, 0x1f_w ; @5
     %2 = add.w %x, %3 ; @4
     %1 = and.w %2, 0x1_w ; @3
     %0 = sub.w %1, %3 ; @2
     ret %0
   }"

let test_srem_by_7 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = rem.w %x, 7_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %4 = mulh.w %x, 0x24924925_w ; @6
     %5 = lsr.w %4, 0x1f_w ; @7
     %3 = add.w %4, %5 ; @5
     %2 = lsl.w %3, 0x3_w ; @4
     %1 = sub.w %2, %3 ; @3
     %0 = sub.w %x, %1 ; @2
     ret %0
   }"

let test_srem_by_8 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = rem.w %x, 8_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %4 = asr.w %x, 0x1f_w ; @6
     %3 = lsr.w %4, 0x1d_w ; @5
     %2 = add.w %x, %3 ; @4
     %1 = and.w %2, 0x7_w ; @3
     %0 = sub.w %1, %3 ; @2
     ret %0
   }"

let test_sel_same _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = eq.w %x, 1_w
     %x = sel.w %c, %x, %x
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     ret %x
   }"

let test_sel_flag _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = eq.w %x, 1_w
     %x = sel.w %c, 1_w, 0_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = eq.w %x, 0x1_w ; @4
     %0 = flag.w %1 ; @3
     ret %0
   }"

let test_sel_flag_neg _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = eq.w %x, 1_w
     %x = sel.w %c, 0_w, 1_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = ne.w %x, 0x1_w ; @4
     %0 = flag.w %1 ; @3
     ret %0
   }"

let test_fold_add _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %y = add.w %x, 1_w
     %z = add.w %x, 1_w
     %r = add.w %y, %z
     ret %r
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = add.w %x, 0x2_w ; @5
     %0 = add.w %x, %1 ; @4
     ret %0
   }"

let test_fold_add_big _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     %x = add.w %x, 1_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = add.w %x, 0x33_w ; @52
     ret %0
   }"

let test_cse_add_simple _ =
  "module foo

   export function w $foo(w %x, w %y) {
   @start:
     %a = add.w %x, %y
     %b = add.w %x, %y
     %c = add.w %a, %b
     ret %c
   }"
  =>
  "module foo

   export function w $foo(w %x, w %y) {
   @0:
     %1 = add.w %x, %y ; @5
     %0 = add.w %1, %1 ; @4
     ret %0
   }"

let test_neg_from_add_not _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = not.w %x
     %x = add.w %x, 1_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = neg.w %x ; @3
     ret %0
   }"

let test_neg_from_add_not_rev _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = not.w %x
     %x = add.w 1_w, %x
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = neg.w %x ; @3
     ret %0
   }"

let test_sub_from_add_neg _ =
  "module foo

   export function w $foo(w %x, w %y) {
   @start:
     %y = neg.w %y
     %x = add.w %x, %y
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x, w %y) {
   @0:
     %0 = sub.w %x, %y ; @3
     ret %0
   }"

let test_sub_from_add_neg_rev _ =
  "module foo

   export function w $foo(w %x, w %y) {
   @start:
     %y = neg.w %y
     %x = add.w %y, %x
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x, w %y) {
   @0:
     %0 = sub.w %x, %y ; @3
     ret %0
   }"

let test_add_from_sub_neg _ =
  "module foo

   export function w $foo(w %x, w %y) {
   @start:
     %y = neg.w %y
     %x = sub.w %x, %y
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x, w %y) {
   @0:
     %0 = add.w %x, %y ; @3
     ret %0
   }"

let test_xor_flag _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = lt.w %x, 5_w
     %f = flag.w %c
     %f = xor.w %f, 1_w
     ret %f
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = ge.w %x, 0x5_w ; @5
     %0 = flag.w %1 ; @4
     ret %0
   }"

let test_double_xor_flag _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = lt.w %x, 5_w
     %f = flag.w %c
     %f = xor.w %f, 1_w
     %f = xor.w %f, 1_w
     ret %f
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = lt.w %x, 0x5_w ; @6
     %0 = flag.w %1 ; @5
     ret %0
   }"

let test_cmp_flag_negate _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = lt.w %x, 5_w
     %f = flag.w %c
     %c = le.w %f, 0_w
     %f = flag.w %c
     ret %f
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = ge.w %x, 0x5_w ; @6
     %0 = flag.w %1 ; @5
     ret %0
   }"

let test_cmp_flag_nop _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = lt.w %x, 5_w
     %f = flag.w %c
     %c = ge.w %f, 1_w
     %f = flag.w %c
     ret %f
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = lt.w %x, 0x5_w ; @6
     %0 = flag.w %1 ; @5
     ret %0
   }"

let suite = "Test optimizations" >::: [
    "Multiply by 1" >:: test_mul_by_1;
    "Multiply by 2" >:: test_mul_by_2;
    "Multiply by 8" >:: test_mul_by_8;
    "Signed divide by 1" >:: test_sdiv_by_1;
    "Signed divide by 4" >:: test_sdiv_by_4;
    "Signed divide by 11" >:: test_sdiv_by_11;
    "Unsigned divide by 8" >:: test_udiv_by_8;
    "Signed remainder by 2" >:: test_srem_by_2;
    "Signed remainder by 7" >:: test_srem_by_7;
    "Signed remainder by 8" >:: test_srem_by_8;
    "Select arms are equal" >:: test_sel_same;
    "Select arms are booleans" >:: test_sel_flag;
    "Select arms are booleans (negated)" >:: test_sel_flag_neg;
    "Folding addition" >:: test_fold_add;
    "Folding addition (big)" >:: test_fold_add_big;
    "CSE (simple addition)" >:: test_cse_add_simple;
    "Negation from add and NOT" >:: test_neg_from_add_not;
    "Negation from add and NOT (reversed)" >:: test_neg_from_add_not_rev;
    "Subtraction from add of neg" >:: test_sub_from_add_neg;
    "Subtraction from add of neg (reversed)" >:: test_sub_from_add_neg_rev;
    "Addition from sub of neg" >:: test_add_from_sub_neg;
    "XOR of flag" >:: test_xor_flag;
    "Double XOR of flag" >:: test_double_xor_flag;
    "Compare flag and negate" >:: test_cmp_flag_negate;
    "Compare flag and NOP" >:: test_cmp_flag_nop;
  ]

let () = run_test_tt_main suite
