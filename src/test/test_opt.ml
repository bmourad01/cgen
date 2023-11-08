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

(* Multiply by 1 is identity. *)
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

(* Strength reduction. *)
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

(* More strength reduction. *)
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

(* More strength reduction. *)
let test_mul_by_11 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = mul.w %x, 11_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = lsl.w %x, 0x3_w ; @3
     %3 = lsl.w %x, 0x1_w ; @5
     %2 = add.w %3, %x ; @4
     %0 = add.w %1, %2 ; @2
     ret %0
   }"

(* More strength reduction. *)
let test_mul_by_26 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = mul.w %x, 26_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = lsl.w %x, 0x5_w ; @3
     %3 = lsl.w %x, 0x2_w ; @5
     %4 = lsl.w %x, 0x1_w ; @6
     %2 = add.w %3, %4 ; @4
     %0 = sub.w %1, %2 ; @2
     ret %0
   }"

(* Division by 1 is identity. *)
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

(* Signed division by -1 is negation. *)
let test_sdiv_by_n1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = div.w %x, 0xffffffff_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = neg.w %x ; @2
     ret %0
   }"

(* Unsigned division by -1 is a test for equality -1. *)
let test_udiv_by_n1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = udiv.w %x, 0xffffffff_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = eq.w %x, 0xffffffff_w ; @3
     %0 = flag.w %1 ; @2
     ret %0
   }"

(* Signed remainder by -1 is 0. *)
let test_srem_by_n1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = rem.w %x, 0xffffffff_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     ret 0x0_w
   }"

(* Unsigned remainder by -1 is %x if %x is not equal to -1,
   and 0 otherwise. *)
let test_urem_by_n1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = urem.w %x, 0xffffffff_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = ne.w %x, 0xffffffff_w ; @3
     %0 = sel.w %1, %x, 0x0_w ; @2
     ret %0
   }"


(* More strength reduction. *)
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

(* More strength reduction. *)
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

(* More strength reduction. *)
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

(* More strength reduction. *)
let test_udiv_by_11 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = udiv.w %x, 11_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = umulh.w %x, 0x1745d175_w ; @2
     ret %0
   }"

(* More strength reduction. *)
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

(* More strength reduction. *)
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

(* More strength reduction. *)
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

(* More strength reduction. *)
let test_urem_by_7 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = urem.w %x, 7_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %3 = umulh.w %x, 0x24924925_w ; @5
     %2 = lsl.w %3, 0x3_w ; @4
     %1 = sub.w %2, %3 ; @3
     %0 = sub.w %x, %1 ; @2
     ret %0
   }"

(* This `sel` instruction is a no-op. *)
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

(* Recognize that the `sel` instruction is simply picking
   a boolean value, which is what `flag` is for. *)
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

(* Same as above, but negated. *)
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

(* Constant folding. *)
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

(* Constant folding on a large expression. *)
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

(* Eliminate the duplicate add. *)
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

(* Recognize two's complement negation. *)
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

(* Same as above, but tests commutativity too. *)
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

(* Add of a negate should be turned into a sub. *)
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

(* Same as above, but tests commutativity too. *)
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

(* Subtract of a negate should be turned into an add. *)
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

(* Recognize that XOR with 1 is flipping %f, which should
   negate the condition in %c. *)
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

(* A double XOR is a no-op. *)
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

(* Testing the flag %f1 to see if it's less or equal to 0
   is equivalent to testing if %f1 is false, so %c1 should
   be negated. *)
let test_cmp_flag_negate _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c1 = lt.w %x, 5_w
     %f1 = flag.w %c1
     %c2 = le.w %f1, 0_w
     %f2 = flag.w %c2
     ret %f2
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = ge.w %x, 0x5_w ; @6
     %0 = flag.w %1 ; @5
     ret %0
   }"

(* Testing the flag %f1 to see if it's greater or equal to 1
   is equivalent to testing if %f1 is true, which is redundant. *)
let test_cmp_flag_nop _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c1 = lt.w %x, 5_w
     %f1 = flag.w %c1
     %c2 = ge.w %f1, 1_w
     %f2 = flag.w %c2
     ret %f2
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %1 = lt.w %x, 0x5_w ; @6
     %0 = flag.w %1 ; @5
     ret %0
   }"

(* A case where a common subexpression can be hoisted up
   the dominator tree. Later, the CFG is simplified to a
   single block. *)
let test_cse_hoist_and_merge _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = sge.w %x, 0_w
     br %c, @pos, @neg
   @pos:
     %a = div.w %x, 4_w
     %r = add.w %a, 1_w
     jmp @end
   @neg:
     %a = div.w %x, 4_w
     %r = add.w %a, 1_w
     jmp @end
   @end:
     ret %r
   }"
  =>
  "module foo

  export function w $foo(w %x) {
  @7:
    %3 = slt.w %x, 0x0_w ; @12
    %4 = add.w %x, 0x3_w ; @13
    %2 = sel.w %3, %4, %x ; @11
    %1 = asr.w %2, 0x2_w ; @10
    %0 = add.w %1, 0x1_w ; @9
    ret %0
  }"

(* The intervals analysis should determine that the value of %x
   in each switch case has been narrowed to a constant, so the
   `add.w` instructions in each case can be folded. *)
let test_switch_case_prop _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     sw.w %x, @default [0x1_w -> @one, 0x2_w -> @two, 0x3_w -> @three]
   @default:
     ret %x
   @one:
     %x = add.w %x, 1_w
     ret %x
   @two:
     %x = add.w %x, 1_w
     ret %x
   @three:
     %x = add.w %x, 1_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @7:
     sw.w %x, @6 [0x1_w -> @4,
                  0x2_w -> @2,
                  0x3_w -> @0]
   @6:
     ret %x
   @4:
     ret 0x2_w
   @2:
     ret 0x3_w
   @0:
     ret 0x4_w
   }"

(* Constant folding across blocks. We end up with a single
   block after edge contraction and block merging. *)
let test_multi_block_fold _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %x = add.w %x, 1_w
     jmp @a
   @a:
     %x = add.w %x, 1_w
     jmp @b
   @b:
     %x = add.w %x, 1_w
     jmp @c
   @c:
     %x = sub.w %x, 1_w
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @6:
     %0 = add.w %x, 0x2_w ; @8
     ret %0
   }"

(* Similar to `test_cse_hoist_and_merge`, but the common
   subexpression must be commuted first. *)
let test_cse_hoist_and_merge_with_commute _ =
  "module foo

   export function w $foo(w %x, w %y) {
   @start:
     %c = eq.w %x, %y
     br %c, @a, @b
   @a:
     %z = add.w %x, %y
     jmp @c
   @b:
     %z = add.w %y, %x
     jmp @c
   @c:
     ret %z
   }"
  =>
  "module foo

   export function w $foo(w %x, w %y) {
   @5:
     %0 = add.w %x, %y ; @7
     ret %0
   }"

(* The path from @start to @next to @zero should reveal to the
   optimizer that the only possible value for %x is 0, and thus
   the `sub.w` instruction can be folded into a constant. Later,
   edge contraction will get rid of the @zero block entirely. *)
let test_cond_prop_1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = slt.w %x, 0_w
     br %c, @neg, @next
   @neg:
     %x = add.w %x, 1_w
     jmp @done
   @next:
     %c = sgt.w %x, 0_w
     br %c, @pos, @zero
   @pos:
     %x = add.w %x, 1_w
     jmp @done
   @zero:
     %x = sub.w %x, 1_w
     jmp @done
   @done:
     ret %x
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @9:
     %0 = slt.w %x, 0x0_w ; @11
     br %0, @7, @5
   @7:
     %1 = add.w %x, 0x1_w ; @12
     jmp @0(%1)
   @5:
     %2 = sgt.w %x, 0x0_w ; @13
     br %2, @3, @0(0xffffffff_w)
   @3:
     %3 = add.w %x, 0x1_w ; @14
     jmp @0(%3)
   @0(%x.4):
     ret %x.4
   }"

(* The condition %c ls always false in the @n block. Later,
   edge contraction should eliminate the @y and @n blocks
   entirely. *)
let test_cond_prop_2 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = lt.w 1_w, %x
     br %c, @y, @n
   @y:
     %r = copy.w 1_w
     jmp @end
   @n:
     %r = flag.w %c
     jmp @end
   @end:
     ret %r
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @5:
     %0 = gt.w %x, 0x1_w ; @7
     br %0, @0(0x1_w), @0(0x0_w)
   @0(%r.3):
     ret %r.3
   }"

(* The computation of %d and %a should be moved to the
   @neg block, since they are used nowhere else. *)
let test_sinking _ =
  "module foo

   export function w $foo(w %x, w %y) {
   @start:
     %a = add.w %x, 1_w
     %d = mul.w %a, 2_w
     %c = slt.w %x, 0_w
     br %c, @neg, @pos
   @neg:
     %b = add.w %d, %y
     jmp @done
   @pos:
     %b = copy.w %y
     jmp @done
   @done:
     ret %b
   }"
  =>
  "module foo

   export function w $foo(w %x, w %y) {
   @5:
     %0 = slt.w %x, 0x0_w ; @9
     br %0, @3, @0(%y)
   @3:
     %3 = add.w %x, 0x1_w ; @12
     %2 = lsl.w %3, 0x1_w ; @11
     %1 = add.w %2, %y ; @10
     jmp @0(%1)
   @0(%b.3):
     ret %b.3
   }"

(* Extend %x to 64 bits and truncate back to 32 bits. *)
let test_trunc_nop_1 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %y = sext.l %x
     %z = itrunc.w %y
     ret %z
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     ret %x
   }"

(* Truncate %x to 32 bits when it already has that type. *)
let test_trunc_nop_2 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %z = itrunc.w %x
     ret %z
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     ret %x
   }"

(* The computation of `add.w %x, 1_w` in @body3 should be
   hoisted all the way to @start. *)
let test_licm_level_3 _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %i = copy.w 0_w
     %z = copy.w 0_w
     jmp @loop1
   @loop1:
     %c = lt.w %i, 10_w
     br %c, @body1, @done
   @body1:
     %j = copy.w 0_w
     jmp @loop2
   @loop2:
     %c = lt.w %j, 10_w
     br %c, @body2, @done2
   @body2:
     %k = copy.w 0_w
     jmp @loop3
   @loop3:
     %c = lt.w %k, 10_w
     br %c, @body3, @done3
   @body3:
     %y = add.w %x, 1_w
     %z = add.w %z, %y
     %k = add.w %k, 1_w
     jmp @loop3
   @done3:
     %j = add.w %j, 1_w
     jmp @loop2
   @done2:
     %i = add.w %i, 1_w
     jmp @loop1
   @done:
     ret %z
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @19:
     %0 = add.w %x, 0x1_w ; @22
     jmp @2(0x0_w, 0x0_w)
   @2(%z.2, %i.2):
     %1 = lt.w %i.2, 0xa_w ; @23
     br %1, @5(%z.2, 0x0_w), @0
   @5(%z.3, %j.2):
     %2 = lt.w %j.2, 0xa_w ; @24
     br %2, @8(%z.3, 0x0_w), @1
   @8(%z.4, %k.2):
     %3 = lt.w %k.2, 0xa_w ; @25
     br %3, @7, @4
   @7:
     %5 = add.w %z.4, %0 ; @27
     %4 = add.w %k.2, 0x1_w ; @26
     jmp @8(%5, %4)
   @4:
     %6 = add.w %j.2, 0x1_w ; @28
     jmp @5(%z.4, %6)
   @1:
     %7 = add.w %i.2, 0x1_w ; @29
     jmp @2(%z.3, %7)
   @0:
     ret %z.2
   }"

(* It is safe to divide by self in @notzero, which should
   yield the result 1. *)
let test_division_by_self _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %c = eq.w %x, 0_w
     br %c, @zero, @notzero
   @zero:
     ret %x
   @notzero:
     %y = div.w %x, %x
     ret %y
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @3:
     %0 = eq.w %x, 0x0_w ; @5
     br %0, @2, @0
   @2:
     ret %x
   @0:
     ret 0x1_w
   }"

(* The initial store to %y should be forwarded to the load
   from %y immediately after. Also, the `urem` is rewritten
   to an `and`. *)
let test_store_to_load_1 _ =
  "module foo

   export function $foo() {
     %x = slot 16, align 16
   @start:
     %y = add.l %x, 8_l
     %m = urem.l %y, 16_l
     %mw = itrunc.w %m
     st.w %mw, %y
     %n = ld.w %y
     st.w %n, $a
     ret
   }"
  =>
  "module foo

   export function $foo() {
     %x = slot 16, align 16
   @0:
     %2 = add.l %x, 0x8_l ; @9
     %1 = and.l %2, 0xf_l ; @8
     %0 = itrunc.w %1 ; @7
     st.w %0, %2 ; @3
     st.w %0, $a ; @1
     ret
   }"

(* The last store to %a in @start can be forwarded to the
   load in @yes. *)
let test_store_to_load_2 _ =
  "module foo

   function w $foo(l %a, l %b, w %x) {
   @start:
     %y = ld.w %a
     st.w %x, %a
     %z = add.w %y, 1_w
     st.w %z, %a
     %c = eq.w %y, 0_w
     br %c, @yes, @no
   @yes:
     %y = ld.w %a
     %d = zext.l %y
     %w = ld.w %d
     jmp @done
   @no:
     %w = ld.w %b
     jmp @done
   @done:
     ret %w
   }"
  =>
  "module foo

   function w $foo(l %a, l %b, w %x) {
   @7:
     %y.1 = ld.w %a ; @12
     st.w %x, %a ; @11
     %0 = add.w %y.1, 0x1_w ; @13
     st.w %0, %a ; @9
     %1 = eq.w %y.1, 0x0_w ; @14
     br %1, @3, @1
   @3:
     %2 = zext.l %0 ; @15
     %w.1 = ld.w %2 ; @4
     jmp @0(%w.1)
   @1:
     %w.2 = ld.w %b ; @2
     jmp @0(%w.2)
   @0(%w.3):
     ret %w.3
   }"

(* Recognize a rotate left by a constant (via `or`). *)
let test_rol_const_or _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %w = lsl.w %x, 5_w
     %y = lsr.w %x, 27_w
     %z = or.w %w, %y
     ret %z
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = rol.w %x, 0x5_w ; @4
     ret %0
   }"

(* Recognize a rotate left by a constant (via `add`). *)
let test_rol_const_add _ =
  "module foo

   export function w $foo(w %x) {
   @start:
     %w = lsl.w %x, 5_w
     %y = lsr.w %x, 27_w
     %z = add.w %w, %y
     ret %z
   }"
  =>
  "module foo

   export function w $foo(w %x) {
   @0:
     %0 = rol.w %x, 0x5_w ; @4
     ret %0
   }"

let test_rle _ =
  "module foo

   export function w $foo(l %x) {
   @start:
      %a = ld.w %x
      %b = ld.w %x
      %c = add.w %a, %b
      ret %c
   }"
  =>
  "module foo

   export function w $foo(l %x) {
   @0:
      %a.1 = ld.w %x ; @3
      %0 = add.w %a.1, %a.1 ; @4
      ret %0
   }"

let suite = "Test optimizations" >::: [
    "Multiply by 1" >:: test_mul_by_1;
    "Multiply by 2" >:: test_mul_by_2;
    "Multiply by 8" >:: test_mul_by_8;
    "Multiply by 11" >:: test_mul_by_11;
    "Multiply by 26" >:: test_mul_by_26;
    "Signed divide by 1" >:: test_sdiv_by_1;
    "Signed divide by -1" >:: test_sdiv_by_n1;
    "Unsigned divide by -1" >:: test_udiv_by_n1;
    "Signed remainder by -1" >:: test_srem_by_n1;
    "Unsigned remainder by -1" >:: test_urem_by_n1;
    "Signed divide by 4" >:: test_sdiv_by_4;
    "Signed divide by 11" >:: test_sdiv_by_11;
    "Unsigned divide by 8" >:: test_udiv_by_8;
    "Unsigned divide by 11" >:: test_udiv_by_11;
    "Signed remainder by 2" >:: test_srem_by_2;
    "Signed remainder by 7" >:: test_srem_by_7;
    "Signed remainder by 8" >:: test_srem_by_8;
    "Unsigned remainder by 7" >:: test_urem_by_7;
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
    "CSE (hoist and merge)" >:: test_cse_hoist_and_merge;
    "Switch case propagation" >:: test_switch_case_prop;
    "Muti-block fold" >:: test_multi_block_fold;
    "CSE (hoist and merge, with commute)" >:: test_cse_hoist_and_merge_with_commute;
    "Conditional propagation 1" >:: test_cond_prop_1;
    "Conditional propagation 2" >:: test_cond_prop_2;
    "Code sinking" >:: test_sinking;
    "Truncate no-op 1" >:: test_trunc_nop_1;
    "Truncate no-op 2" >:: test_trunc_nop_2;
    "LICM (level 3)" >:: test_licm_level_3;
    "Division by self" >:: test_division_by_self;
    "Store to load forwarding 1" >:: test_store_to_load_1;
    "Store to load forwarding 2" >:: test_store_to_load_2;
    "Test rotate left by constant and OR" >:: test_rol_const_or;
    "Test rotate left by constant and addition" >:: test_rol_const_add;
    "Redundant load elimination" >:: test_rle;
  ]

let () = run_test_tt_main suite
