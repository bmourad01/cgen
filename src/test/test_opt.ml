open Core
open OUnit2
open Cgen

let compare_outputs ?(chop_end = true) expected_file actual =
  Golden.compare_or_update ()
    ~chop_end
    ~expected_file
    ~actual
    ~fail:assert_failure

let from_file filename =
  let open Context.Syntax in
  let* m = Parse.Virtual.from_file filename in
  let* tenv, m = Passes.initialize m in
  Passes.optimize tenv m

let from_file_abi filename =
  let open Context.Syntax in
  let* tenv, m = from_file filename in
  let* m = Passes.to_abi tenv m in
  let* () = Context.iter_seq_err (Virtual.Abi.Module.funs m) ~f:Passes.Ssa.check_abi in
  Passes.optimize_abi m

let test ?(f = from_file) name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = filename ^ ".opt" in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.eval begin
    let open Context.Syntax in
    let* _, m = f filename in
    let* () = Virtual.Module.funs m |> Context.iter_seq_err ~f:Passes.Ssa.check in
    !!(Format.asprintf "%a" Virtual.Module.pp m)
  end |> function
  | Ok p' -> compare_outputs filename' p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let coalesce_only filename =
  let open Context.Syntax in
  let* m = Parse.Virtual.from_file filename in
  let* tenv, m = Passes.initialize m in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Coalesce_slots.run in
  let*? m = Virtual.Module.map_funs_err m ~f:Passes.Resolve_constant_blk_args.run in
  let+? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
  tenv, m

let test_destructure name _ =
  let filename = Format.sprintf "data/opt/%s.sir" name in
  let filename' = Format.sprintf "%s.vir" filename in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = Parse.Structured.from_file filename in
    let* m = Passes.destructure m in
    !!(Format.asprintf "%a" Virtual.Module.pp m)
  end |> function
  | Ok p' -> compare_outputs filename' p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let test_restructure ?(opt = false) name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = Format.sprintf "%s%s.sir" filename
      (if opt then ".opt" else "") in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = Parse.Virtual.from_file filename in
    let* tenv, m = Passes.initialize m in
    let* tenv, m = if opt
      then Passes.optimize tenv m
      else !!(tenv, m) in
    let* m = Passes.restructure ~tenv m in
    !!(Format.asprintf "%a" Structured.Module.pp m)
  end |> function
  | Ok p' -> compare_outputs filename' p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let test_abi target ext name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = Format.sprintf "%s.opt.%s" filename ext in
  Context.init target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = from_file_abi filename in
    !!(Format.asprintf "%a" Virtual.Abi.Module.pp m)
  end |> function
  | Ok p' -> compare_outputs filename' p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let test_isel target abi ext name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = Format.sprintf "%s.opt.%s.%s" filename abi ext in
  Context.init target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = from_file_abi filename in
    let* (module Machine) = Context.machine in
    let* m = Passes.isel (module Machine) m in
    let module Remove_deads = Pseudo_passes.Remove_dead_insns(Machine) in
    let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
    !!(Format.asprintf "%a" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m)
  end |> function
  | Ok p' -> compare_outputs filename' p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let test_regalloc target abi ext name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = Format.sprintf "%s.opt.%s.%s.regalloc" filename abi ext in
  Context.init target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = from_file_abi filename in
    let* (module Machine) = Context.machine in
    let* m = Passes.isel (module Machine) m in
    let module Remove_deads = Pseudo_passes.Remove_dead_insns(Machine) in
    let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
    let* m = Passes.regalloc (module Machine) m in
    let m = Pseudo.Module.map_funs m ~f:Machine.Peephole.run in
    let m = Pseudo.Module.map_funs m ~f:Remove_deads.run in
    !!(Format.asprintf "%a" (Pseudo.Module.pp Machine.Insn.pp Machine.Reg.pp) m)
  end |> function
  | Ok p' -> compare_outputs filename' p'
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let compile_c_driver asm driver exe =
  let p = Process.run "cc" [asm; driver; "-o"; exe; "-g"; "-fno-omit-frame-pointer"] in
  match p.code with
  | Shexp_process.Exit_status.Exited n ->
    Context.unless (n = 0) @@ fun () ->
    Context.failf "failed to compile C driver program %s (error code %d): %s"
      driver n p.stderr ()
  | Shexp_process.Exit_status.Signaled n ->
    Context.failf "failed to compile C driver program %s (signaled %d): %s"
      driver n p.stderr ()

let output_asm m file =
  let open Context.Syntax in
  let oc = Out_channel.create file in
  let fmt = Format.formatter_of_out_channel oc in
  let+ () = Passes.to_asm fmt m in
  Out_channel.close oc

let test_native target abi ext name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let driver = Format.sprintf "data/opt/%s.driver.%s.%s" name abi ext in
  let driver_c = driver ^ ".c" in
  let driver_output = driver ^ ".output" in
  let tmpname = Format.asprintf "cgen-%s-%s-%s" name abi ext in
  let exe = Format.sprintf "/tmp/%s" tmpname in
  let asm = Format.sprintf "/tmp/%s.S" tmpname in
  Context.init target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = from_file_abi filename in
    let* () = output_asm m asm in
    let+ () = compile_c_driver asm driver_c exe in
    Process.run exe []
  end |> function
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err
  | Ok p ->
    begin match p.code with
      | Shexp_process.Exit_status.Exited n ->
        let msg = Format.sprintf
            "Unexpected return code: got %d, expected 0\n\n\
             STDERR:\n%s\n" n p.stderr in
        assert_bool msg (n = 0)
      | Shexp_process.Exit_status.Signaled n ->
        assert_failure @@ Format.sprintf
          "Process signaled %d, expected return code 0\n\n\
           STDERR:\n:%s\n" n p.stderr
    end;
    if Shexp_process.(eval @@ file_exists driver_output) then
      compare_outputs ~chop_end:false driver_output p.stdout

(* Specific ABI lowering tests. *)
let test_sysv = test_abi Machine.X86.Amd64_sysv.target "sysv"

(* Specific instruction selection tests. *)
let test_sysv_amd64 = test_isel Machine.X86.Amd64_sysv.target "sysv" "amd64"

(* Specific register allocation tests. *)
let test_sysv_amd64_regalloc = test_regalloc Machine.X86.Amd64_sysv.target "sysv" "amd64"

(* Specific native tests. *)
let test_sysv_amd64_native = test_native Machine.X86.Amd64_sysv.target "sysv" "amd64"

(* Destructuring tests *)
let destructure_suite = "Test destructure" >::: [
    "Fibonacci" >:: test_destructure "fib";
    "Switch 1" >:: test_destructure "switch1";
    "Goto 1" >:: test_destructure "goto1";
    "GCD" >:: test_destructure "gcd";
  ]

let to_restructure = [
  "Collatz", "collatz";
  "Collatz (recursive)", "collatz_rec";
  "Binary search", "bsearch";
  "Quicksort", "qsort";
]

(* Restructuring tests (without optimizations) *)
let restructure_suite = "Test restructure (without optimizations)" >::: begin
    List.map to_restructure ~f:(fun (n, f) ->
        n >:: test_restructure f)
  end

(* Restructuring tests (with optimizations) *)
let restructure_opt_suite = "Test restructure (with optimizations)" >::: begin
    List.map to_restructure ~f:(fun (n, f) ->
        n >:: test_restructure ~opt:true f)
  end

(* General optimization tests *)
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
    "XOR to OR" >:: test "xor_to_or";
    "Double XOR of flag" >:: test "doublexorflag";
    "Compare flag and negate" >:: test "cmpflagnegate";
    "Compare flag and NOP" >:: test "cmpflagnop";
    "CSE (hoist)" >:: test "csehoist";
    "CSE (hoist and merge)" >:: test "csehoistandmerge";
    "CSE (hoist and merge 2)" >:: test "csehoistandmerge2";
    "CSE (hoist and merge 3)" >:: test "csehoistandmerge3";
    "Switch case propagation" >:: test "switchcaseprop";
    "Switch simplification" >:: test "switchsimpl";
    "Switch simplification 2" >:: test "sw";
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
    "Prime numbers driver (LICM)" >:: test "prime_main_licm";
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
    "Collatz (recursive)" >:: test "collatz_rec";
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
    "Naiive even-odd test" >:: test "evenodd";
    "Trivial infinite loop" >:: test "forever";
    "Tail-recursive infinite loop" >:: test "forever2";
    "CLZ/CTZ 8-bit" >:: test "clz_ctz_8";
    "POPCNT" >:: test "popcnt";
    "Compare slots" >:: test "cmpslot";
    "Add to slot" >:: test "slotadd1";
    "Branch to non-label 1" >:: test "brind";
    "Dragon" >:: test "dragon";
    "Quicksort" >:: test "qsort";
    "Palindrome" >:: test "palindrome";
    "Integer pow" >:: test "int_pow";
    "AND test" >:: test "and_test";
    "No sinking" >:: test "nosink";
    "Spill test 2" >:: test "spill2";
    "Parallel moves" >:: test "parallel";
    "SROA" >:: test "sroa";
    "Sink 1" >:: test "sink1";
    "Escape 1" >:: test "esc1";
    "Slot coalesce 1 (no other opts)" >:: test ~f:coalesce_only "coalesce1";
    "Slot coalesce 1 (full opts)" >:: test "coalesce1a";
    "Bad load 1" >:: test "badload1";
    "Bad load 2" >:: test "badload2";
    "Binary search" >:: test "bsearch";
  ]

let abi_suite = "Test ABI lowering" >::: [
    (* SysV ABI lowering tests *)
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
    "Naiive even-odd test (SysV)" >:: test_sysv "evenodd";
    "Trivial infinite loop (SysV)" >:: test_sysv "forever";
    "Tail-recursive infinite loop (SysV)" >:: test_sysv "forever2";
    "Switch simplification 2 (SysV)" >:: test_sysv "sw";
    "CLZ/CTZ 8-bit (SysV)" >:: test_sysv "clz_ctz_8";
    "POPCNT (SysV)" >:: test_sysv "popcnt";
    "Short-circuiting AND (flag indirection) (SysV)" >:: test_sysv "shortcircand2";
    "Compare slots (SysV)" >:: test_sysv "cmpslot";
    "Add to slot (SysV)" >:: test_sysv "slotadd1";
    "XOR to OR (SysV)" >:: test_sysv "xor_to_or";
    "Branch to non-label 1 (SysV)" >:: test_sysv "brind";
    "Dragon (SysV)" >:: test_sysv "dragon";
    "Collatz (SysV)" >:: test_sysv "collatz";
    "Collatz recursive (SysV)" >:: test_sysv "collatz_rec";
    "Ackermann (SysV)" >:: test_sysv "ackermann";
    "Quicksort (SysV)" >:: test_sysv "qsort";
    "Binary search (SysV)" >:: test "bsearch";
  ]

let isel_suite = "Test instruction selection" >::: [
    (* AMD64 instruction selection tests *)
    "LEA arithmetic with negative disp (SysV AMD64)" >:: test_sysv_amd64 "lea1";
    "Test prime numbers (SysV AMD64)" >:: test_sysv_amd64 "prime";
    "Switch case propagation (SysV AMD64)" >:: test_sysv_amd64 "switchcaseprop";
    "Slot promotion 2 (GCD, partial) (SysV AMD64)" >:: test_sysv_amd64 "promote2-partial";
    "Variadic function arguments 1 (SysV AMD64)" >:: test_sysv_amd64 "vaarg1";
    "Variadic sum (SysV AMD64)" >:: test_sysv_amd64 "vasum";
    "Sum an array of words (SysV AMD64)" >:: test_sysv_amd64 "sumarray";
    "Copy an array of words (SysV AMD64)" >:: test_sysv_amd64 "cpyarray";
    "Folding addition (SysV AMD64)" >:: test_sysv_amd64 "foldadd";
    "Unsigned remainder by 7 (SysV AMD64)" >:: test_sysv_amd64 "uremby7";
    "Edge contraction and select (SysV AMD64)" >:: test_sysv_amd64 "contractsel";
    "Naiive even-odd test (SysV AMD64)" >:: test_sysv_amd64 "evenodd";
    "Trivial infinite loop (SysV AMD64)" >:: test_sysv_amd64 "forever";
    "Tail-recursive infinite loop (SysV AMD64)" >:: test_sysv_amd64 "forever2";
    "Switch simplification 2 (SysV AMD64)" >:: test_sysv_amd64 "sw";
    "CLZ/CTZ 8-bit (SysV AMD64)" >:: test_sysv_amd64 "clz_ctz_8";
    "POPCNT (SysV AMD64)" >:: test_sysv_amd64 "popcnt";
    "Short-circuiting AND (flag indirection) (SysV AMD64)" >:: test_sysv_amd64 "shortcircand2";
    "Compare slots (SysV AMD64)" >:: test_sysv_amd64 "cmpslot";
    "Add to slot (SysV AMD64)" >:: test_sysv_amd64 "slotadd1";
    "XOR to OR (SysV AMD64)" >:: test_sysv_amd64 "xor_to_or";
    "Branch to non-label 1 (SysV AMD64)" >:: test_sysv_amd64 "brind";
    "Dragon (SysV AMD64)" >:: test_sysv_amd64 "dragon";
    "Collatz (SysV AMD64)" >:: test_sysv_amd64 "collatz";
    "Collatz recursive (SysV AMD64)" >:: test_sysv_amd64 "collatz_rec";
    "Ackermann (SysV AMD64)" >:: test_sysv_amd64 "ackermann";
    "Quicksort (SysV AMD64)" >:: test_sysv_amd64 "qsort";
    "Parallel moves (SysV AMD64)" >:: test_sysv_amd64 "parallel";
    "Binary search (SysV AMD64)" >:: test_sysv_amd64 "bsearch";
  ]

let regalloc_suite = "Test register allocation" >::: [
    (* AMD64 register allocation tests *)
    "LEA arithmetic with negative disp (SysV AMD64)" >:: test_sysv_amd64_regalloc "lea1";
    "Test prime numbers (SysV AMD64)" >:: test_sysv_amd64_regalloc "prime";
    "Spill test 1 (SysV AMD64)" >:: test_sysv_amd64_regalloc "spill1";
    "Copy an array of words (SysV AMD64)" >:: test_sysv_amd64_regalloc "cpyarray";
    "Folding addition (SysV AMD64)" >:: test_sysv_amd64_regalloc "foldadd";
    "Unsigned remainder by 7 (SysV AMD64)" >:: test_sysv_amd64_regalloc "uremby7";
    "Edge contraction and select (SysV AMD64)" >:: test_sysv_amd64_regalloc "contractsel";
    "Prime numbers driver (SysV AMD64)" >:: test_sysv_amd64_regalloc "prime_main_licm";
    "Unordered CSE (SysV AMD64)" >:: test_sysv_amd64_regalloc "unordered";
    "Signed remainder by 7 (SysV AMD64)" >:: test_sysv_amd64_regalloc "sremby7";
    "Signed division by -5 (SysV AMD64)" >:: test_sysv_amd64_regalloc "sdivbyn5";
    "Scalar arguments passed on the stack (SysV AMD64)" >:: test_sysv_amd64_regalloc "stkarg";
    "Naiive even-odd test (SysV AMD64)" >:: test_sysv_amd64_regalloc "evenodd";
    "Variadic function arguments 1 (SysV AMD64)" >:: test_sysv_amd64_regalloc "vaarg1";
    "Trivial infinite loop (SysV AMD64)" >:: test_sysv_amd64_regalloc "forever";
    "Tail-recursive infinite loop (SysV AMD64)" >:: test_sysv_amd64_regalloc "forever2";
    "Switch simplification 2 (SysV AMD64)" >:: test_sysv_amd64_regalloc "sw";
    "CLZ/CTZ 8-bit (SysV AMD64)" >:: test_sysv_amd64_regalloc "clz_ctz_8";
    "POPCNT (SysV AMD64)" >:: test_sysv_amd64_regalloc "popcnt";
    "Short-circuiting AND (flag indirection) (SysV AMD64)" >:: test_sysv_amd64_regalloc "shortcircand2";
    "Compare slots (SysV AMD64)" >:: test_sysv_amd64_regalloc "cmpslot";
    "Add to slot (SysV AMD64)" >:: test_sysv_amd64_regalloc "slotadd1";
    "XOR to OR (SysV AMD64)" >:: test_sysv_amd64_regalloc "xor_to_or";
    "Branch to non-label 1 (SysV AMD64)" >:: test_sysv_amd64_regalloc "brind";
    "Dragon (SysV AMD64)" >:: test_sysv_amd64_regalloc "dragon";
    "Collatz (SysV AMD64)" >:: test_sysv_amd64_regalloc "collatz";
    "Collatz recursive (SysV AMD64)" >:: test_sysv_amd64_regalloc "collatz_rec";
    "Ackermann (SysV AMD64)" >:: test_sysv_amd64_regalloc "ackermann";
    "Quicksort (SysV AMD64)" >:: test_sysv_amd64_regalloc "qsort";
    "Quicksort, swap inlined (SysV AMD64)" >:: test_sysv_amd64_regalloc "qsort_inline_swap";
    "Palindrome (SysV AMD64)" >:: test_sysv_amd64_regalloc "palindrome";
    "Integer pow (SysV AMD64)" >:: test_sysv_amd64_regalloc "int_pow";
    "AND test (SysV AMD64)" >:: test_sysv_amd64_regalloc "and_test";
    "No sinking (SysV AMD64)" >:: test_sysv_amd64_regalloc "nosink";
    "Spill test 2 (SysV AMD64)" >:: test_sysv_amd64_regalloc "spill2";
    "Analyze array (SysV AMD64)" >:: test_sysv_amd64_regalloc "analyze_array";
    "Slot promotion 2 (GCD, partial) (SysV AMD64)" >:: test_sysv_amd64_regalloc "promote2-partial";
    "Parallel moves (SysV AMD64)" >:: test_sysv_amd64_regalloc "parallel";
    "Struct in a block argument (SysV AMD64)" >:: test_sysv_amd64_regalloc "sumphi";
    "Variadic sum (SysV AMD64)" >:: test_sysv_amd64_regalloc "vasum";
    "Binary search (SysV AMD64)" >:: test_sysv_amd64_regalloc "bsearch";
  ]

let native_suite = "Test native code" >::: [
    (* AMD64 SysV *)
    "First 20 prime numbers (SysV AMD64)" >:: test_sysv_amd64_native "prime";
    "Extended GCD (SysV AMD64)" >:: test_sysv_amd64_native "gcdext";
    "Copy array (SysV AMD64)" >:: test_sysv_amd64_native "cpyarray";
    "Variadic sum (SysV AMD64)" >:: test_sysv_amd64_native "vasum";
    "Collatz (SysV AMD64)" >:: test_sysv_amd64_native "collatz";
    "Collatz recursive (SysV AMD64)" >:: test_sysv_amd64_native "collatz_rec";
    "Ackermann (SysV AMD64)" >:: test_sysv_amd64_native "ackermann";
    "CLZ/CTZ 8-bit (SysV AMD64)" >:: test_sysv_amd64_native "clz_ctz_8";
    "POPCNT (SysV AMD64)" >:: test_sysv_amd64_native "popcnt";
    "Quicksort (SysV AMD64)" >:: test_sysv_amd64_native "qsort";
    "Quicksort, swap inlined (SysV AMD64)" >:: test_sysv_amd64_native "qsort_inline_swap";
    "Spill test 1 (SysV AMD64)" >:: test_sysv_amd64_native "spill1";
    "Variadic function arguments 1 (SysV AMD64)" >:: test_sysv_amd64_native "vaarg1";
    "Variadic function arguments 2 (SysV AMD64)" >:: test_sysv_amd64_native "vaarg2";
    "Palindrome (SysV AMD64)" >:: test_sysv_amd64_native "palindrome";
    "Integer pow (SysV AMD64)" >:: test_sysv_amd64_native "int_pow";
    "AND test (SysV AMD64)" >:: test_sysv_amd64_native "and_test";
    "No sinking (SysV AMD64)" >:: test_sysv_amd64_native "nosink";
    "Spill test 2 (SysV AMD64)" >:: test_sysv_amd64_native "spill2";
    "Analyze array (SysV AMD64)" >:: test_sysv_amd64_native "analyze_array";
    "Unsigned remainder by 7 (SysV AMD64)" >:: test_sysv_amd64_native "uremby7";
    "Slot promotion 2 (GCD, partial) (SysV AMD64)" >:: test_sysv_amd64_native "promote2-partial";
    "Struct in a block argument (SysV AMD64)" >:: test_sysv_amd64_native "sumphi";
    "Returning, passing, and dereferencing a struct (SysV AMD64)" >:: test_sysv_amd64_native "unref";
    "Sink 1 (SysV AMD64)" >:: test_sysv_amd64_native "sink1";
    "Binary search (SysV AMD64)" >:: test_sysv_amd64_native "bsearch";
  ]

let () = run_test_tt_main @@ test_list [
    destructure_suite;
    restructure_suite;
    restructure_opt_suite;
    opt_suite;
    abi_suite;
    isel_suite;
    regalloc_suite;
    native_suite;
  ]
