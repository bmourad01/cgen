open Core
open Regular.Std
open OUnit2
open Cgen

(* Ignore certain characters when comparing the output *)
let fmt = String.filter ~f:(function
    | '\r' | '\n' | '\t' | ' ' -> false
    | _ -> true)

let from_file filename =
  let open Context.Syntax in
  let* m = Parse.Virtual.from_file filename in
  let* tenv, m = Passes.initialize m in
  Passes.optimize tenv m

let compare_outputs expected p' =
  let msg = Format.asprintf "Expected:@,@[%s@]@,Got:@,@[%s@]" expected p' in
  assert_equal (fmt p') (fmt expected) ~msg ~cmp:String.equal

let from_file_abi filename =
  let open Context.Syntax in
  let* tenv, m = from_file filename in
  let* m = Passes.to_abi tenv m in
  let* () = Context.iter_seq_err (Virtual.Abi.Module.funs m) ~f:Passes.Ssa.check_abi in
  Passes.optimize_abi m

let test name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = filename ^ ".expected" in
  let expected = In_channel.read_all filename' in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.eval begin
    let open Context.Syntax in
    let* _, m = from_file filename in
    let* () = Virtual.Module.funs m |> Context.iter_seq_err ~f:Passes.Ssa.check in
    !!(Format.asprintf "%a" Virtual.Module.pp m)
  end |> function
  | Ok p' -> compare_outputs expected p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let test_abi target ext name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = Format.sprintf "%s.expected.%s" filename ext in
  let expected = In_channel.read_all filename' in
  Context.init target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = from_file_abi filename in
    !!(Format.asprintf "%a" Virtual.Abi.Module.pp m)
  end |> function
  | Ok p' -> compare_outputs expected p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let isel m ~f =
  let open Context.Syntax in
  let+ funs =
    Virtual.Abi.Module.funs m |>
    Context.Seq.map ~f >>|
    Seq.to_list in
  Pseudo.Module.create ()
    ~dict:(Virtual.Abi.Module.dict m)
    ~data:(Virtual.Abi.Module.data m |> Seq.to_list)
    ~name:(Virtual.Abi.Module.name m) ~funs

let test_isel target ext name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = Format.sprintf "%s.expected.%s" filename ext in
  let expected = In_channel.read_all filename' in
  Context.init target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = from_file_abi filename in
    let* (module Machine) = Context.machine in
    let module Isel = Isel.Make(Machine)(Context) in
    let* m = isel m ~f:Isel.run in
    let module Remove_deads = Pseudo.Remove_dead_insns(Machine) in
    let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
    !!(Format.asprintf "%a" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m)
  end |> function
  | Ok p' -> compare_outputs expected p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

(* Specific ABI lowering tests. *)
let test_sysv = test_abi Machine.X86.Amd64_sysv.target "sysv"

(* Specific instruction selection tests. *)
let test_amd64 = test_isel Machine.X86.Amd64_sysv.target "amd64"

(*  General optimization tests *)
let opt_suite = "Test optimizations" >::: [
    "Multiply by 1" >:: test "mulby1";
    "Multiply by 2" >:: test "mulby2";
    "Multiply by 8" >:: test "mulby8";
    "Multiply by 11" >:: test "mulby11";
    "Multiply by 26" >:: test "mulby26";
    "Multiply by int min + 1" >:: test "mulbyminsignedplus1";
    "Signed divide by 1" >:: test "sdivby1";
    "Signed divide by -1" >:: test "sdivbyn1";
    "Unsigned divide by -1" >:: test "udivbyn1";
    "Signed remainder by -1" >:: test "srembyn1";
    "Unsigned remainder by -1" >:: test "urembyn1";
    "Signed divide by 4" >:: test "sdivby4";
    "Signed divide by 11" >:: test "sdivby11";
    "Signed divide by -5" >:: test "sdivbyn5";
    "Unsigned divide by 8" >:: test "udivby8";
    "Unsigned divide by 11" >:: test "udivby11";
    "Signed remainder by 2" >:: test "sremby2";
    "Signed remainder by 7" >:: test "sremby7";
    "Signed remainder by 8" >:: test "sremby8";
    "Unsigned remainder by 7" >:: test "uremby7";
    "Select arms are equal" >:: test "selsame";
    "Select arms are booleans" >:: test "selflag";
    "Select arms are booleans (negated)" >:: test "selflagneg";
    "Folding addition" >:: test "foldadd";
    "Folding addition (big)" >:: test "foldaddbig";
    "CSE (simple addition)" >:: test "cseaddsimple";
    "Negation from add and NOT" >:: test "negfromaddnot";
    "Negation from add and NOT (reversed)" >:: test "negfromaddnotrev";
    "Negation from NOT and add" >:: test "negfromnotadd";
    "Negation from NOT and add (reversed)" >:: test "negfromnotaddrev";
    "Negation from NOT and sub" >:: test "negfromnotsub";
    "Subtraction from add of neg" >:: test "subfromaddneg";
    "Subtraction from add of neg (reversed)" >:: test "subfromaddnegrev";
    "Addition from sub of neg" >:: test "addfromsubneg";
    "XOR of flag" >:: test "xorflag";
    "Double XOR of flag" >:: test "doublexorflag";
    "Compare flag and negate" >:: test "cmpflagnegate";
    "Compare flag and NOP" >:: test "cmpflagnop";
    "CSE (hoist)" >:: test "csehoist";
    "CSE (hoist and merge)" >:: test "csehoistandmerge";
    "CSE (hoist and merge 2)" >:: test "csehoistandmerge2";
    "CSE (hoist and merge 3)" >:: test "csehoistandmerge3";
    "Switch case propagation" >:: test "switchcaseprop";
    "Switch simplification" >:: test "switchsimpl";
    "Muti-block fold" >:: test "multiblockfold";
    "CSE (hoist and merge, with commute)" >:: test "csehoistandmergecommute";
    "Conditional propagation 1" >:: test "condprop1";
    "Conditional propagation 2" >:: test "condprop2";
    "Code sinking" >:: test "sinking";
    "Truncate no-op 1" >:: test "truncnop1";
    "Truncate no-op 2" >:: test "truncnop2";
    "LICM (level 1)" >:: test "licmlevel1";
    "LICM (level 2)" >:: test "licmlevel2";
    "LICM (level 3)" >:: test "licmlevel3";
    "Division by self" >:: test "divisionbyself";
    "Remainder of self" >:: test "remainderofself";
    "Store to load forwarding 1" >:: test "storetoload1";
    "Store to load forwarding 2" >:: test "storetoload2";
    "Test rotate left by constant and OR" >:: test "rolconstor";
    "Test rotate left by constant and addition" >:: test "rolconstadd";
    "Redundant load elimination" >:: test "rle";
    "Redundant load elimination (partial redundancy)" >:: test "rle-partial";
    "Test prime numbers" >:: test "prime";
    "Test strcmp RLE" >:: test "strcmprle";
    "Test strcmp non-RLE" >:: test "strcmpnonrle";
    "Test reassoc add right" >:: test "reassocaddright";
    "Test reassoc add left" >:: test "reassocaddleft";
    "Test reassoc add const" >:: test "reassocaddconst";
    "Sum an array of words" >:: test "sumarray";
    "Copy an array of words" >:: test "cpyarray";
    "Constant select" >:: test "constsel";
    "Slot promotion 1" >:: test "promote1";
    "Slot promotion 2 (GCD)" >:: test "promote2";
    "Slot promotion 2 (GCD, partial)" >:: test "promote2-partial";
    "Tail recursion elimination 1 (factorial)" >:: test "tailrec1";
    "Tail recursion elimination 2 (fibonacci)" >:: test "tailrec2";
    "Constant phi" >:: test "constphi";
    "Collatz (promotion)" >:: test "collatz";
    "Ackermann" >:: test "ackermann";
    "Branchless" >:: test "branchless";
    "LICM (sinking)" >:: test "licmsink";
    "LICM (sinking 2)" >:: test "licmsink2";
    "Short-circuiting AND" >:: test "shortcircand";
    "Short-circuiting AND (flag indirection)" >:: test "shortcircand2";
    "Short-circuiting AND (negated flag indirection)" >:: test "shortcircand3";
    "Short-circuiting OR" >:: test "shortcircor";
    "Short-circuiting OR (flag indirection)" >:: test "shortcircor2";
    "Short-circuiting OR (negated flag indirection)" >:: test "shortcircor3";
    "Edge contraction and select" >:: test "contractsel";
  ]

(* SysV ABI lowering tests *)
let abi_suite = "Test ABI lowering" >::: [
    "Simple calls (SysV)" >:: test_sysv "addcalls";
    "Empty struct (SysV)" >:: test_sysv "emptystruct";
    "Extended GCD returning a struct (SysV)" >:: test_sysv "gcdext";
    "Extended GCD with pointer params (SysV)" >:: test_sysv "gcdextm";
    "Constructing and returning a struct (SysV)" >:: test_sysv "retmem";
    "Scalar arguments passed on the stack (SysV)" >:: test_sysv "stkarg";
    "Struct in a block argument (SysV)" >:: test_sysv "sumphi";
    "Returning, passing, and dereferencing a struct (SysV)" >:: test_sysv "unref";
    "Variadic function arguments 1 (SysV)" >:: test_sysv "vaarg1";
    "Variadic function arguments 2 (SysV)" >:: test_sysv "vaarg2";
    "Variadic sum (SysV)" >:: test_sysv "vasum";
    "Unsigned integer to float (SysV)" >:: test_sysv "uitof";
  ]

(* AMD64 instruction selection tests *)
let isel_suite = "Test instruction selection" >::: [
    "LEA arithmetic with negative disp (AMD64)" >:: test_amd64 "lea1";
    "Test prime numbers (AMD64)" >:: test_amd64 "prime";
    "Switch case propagation (AMD64)" >:: test_amd64 "switchcaseprop";
    "Slot promotion 2 (GCD, partial) (AMD64)" >:: test_amd64 "promote2-partial";
    "Variadic function arguments 1 (AMD64)" >:: test_amd64 "vaarg1";
    "Variadic sum (AMD64)" >:: test_amd64 "vasum";
    "Sum an array of words (AMD64)" >:: test_amd64 "sumarray";
    "Copy an array of words (AMD64)" >:: test_amd64 "cpyarray";
    "Folding addition (AMD64)" >:: test_amd64 "foldadd";
    "Unsigned remainder by 7 (AMD64)" >:: test_amd64 "uremby7";
    "Edge contraction and select" >:: test_amd64 "contractsel";
  ]

let () = run_test_tt_main @@ test_list [
    opt_suite;
    abi_suite;
    isel_suite;
  ]
