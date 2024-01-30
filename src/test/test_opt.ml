open Core
open OUnit2
open Cgen

(* Ignore certain characters when comparing the output *)
let fmt = String.filter ~f:(function
    | '\r' | '\n' | '\t' | ' ' -> false
    | _ -> true)

let test name _ =
  let filename = Format.sprintf "data/opt/%s.vir" name in
  let filename' = filename ^ ".expected" in
  let expected = In_channel.read_all filename' in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.eval begin
    let open Context.Syntax in
    let* target = Context.target in
    let* m = Parse.Virtual.from_file filename in
    let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
    let*? tenv = Typecheck.run m ~target in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Ssa.run in
    let*? m = Virtual.Module.map_funs_err m ~f:(Passes.Sccp.run tenv) in
    let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
    let* m = Context.Virtual.Module.map_funs m ~f:Passes.Simplify_cfg.run in
    let* m = Context.Virtual.Module.map_funs m ~f:(Passes.Egraph_opt.run tenv) in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
    let m = Virtual.Module.map_funs m ~f:Passes.Remove_disjoint_blks.run in
    let* m = Context.Virtual.Module.map_funs m ~f:Passes.Simplify_cfg.run in
    let*? m = Virtual.Module.map_funs_err m ~f:Passes.Remove_dead_vars.run in
    !!(Format.asprintf "%a" Virtual.Module.pp m)
  end |> function
  | Error err ->
    assert_failure @@ Format.asprintf "%a" Error.pp err
  | Ok p' ->
    let msg = Format.asprintf "Expected:@,@[%s@]@,Got:@,@[%s@]" expected p' in
    assert_equal (fmt p') (fmt expected) ~msg ~cmp:String.equal

let suite = "Test optimizations" >::: [
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
    "CSE (hoist and merge)" >:: test "csehoistandmerge";
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
    "Test prime numbers" >:: test "prime";
    "Test strcmp RLE" >:: test "strcmprle";
    "Test strcmp non-RLE" >:: test "strcmpnonrle";
    "Test reassoc add right" >:: test "reassocaddright";
    "Test reassoc add left" >:: test "reassocaddleft";
    "Test reassoc add const" >:: test "reassocaddconst";
    "Sum an array of words" >:: test "sumarray";
    "Constant select" >:: test "constsel";
  ]

let () = run_test_tt_main suite
