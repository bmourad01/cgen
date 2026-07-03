open Core
open OUnit2

module C = Cgen_c
module Context = Cgen.Context
module Passes = Cgen.Passes
module Structured = Cgen.Structured
module Virtual = Cgen.Virtual
module Machine = Cgen.Machine

let compare_outputs ?(chop_end = true) expected_file actual =
  Golden.compare_or_update ()
    ~chop_end
    ~expected_file
    ~actual
    ~fail:assert_failure

let dmodel =
  C.Data_model.create
    ~model:C.Data_model.LP64
    ~char_signed:true
    ~va_list_size:24
    ~va_list_align:8

let elaborate u = C.Elab.elab u ~dmodel ~loc_of_ann:Option.some

let parse ~preprocess file =
  let cpp = if preprocess then Some C.Parse.Cpp.default else None in
  C.Parse.from_file ?cpp file

let ok name = Format.sprintf "data/c/ok/%s.c" name
let fail name = Format.sprintf "data/c/fail/%s.c" name

let test_parse ?(preprocess = false) name _ =
  let file = ok name in
  match parse ~preprocess file with
  | Error d -> assert_failure @@ Cgen_utils.Diagnostic.to_string d
  | Ok u -> compare_outputs (file ^ ".parse") (C.Cunit.to_string u)

let test_elab ?(preprocess = false) name _ =
  let file = ok name in
  match parse ~preprocess file with
  | Error d -> assert_failure @@ Cgen_utils.Diagnostic.to_string d
  | Ok u -> match elaborate u with
    | Error d -> assert_failure @@ Cgen_utils.Diagnostic.to_string d
    | Ok (t, _warnings) -> compare_outputs (file ^ ".elab") (C.Tcunit.to_string t)

let test_error name _ =
  let file = fail name in
  let diag = match C.Parse.from_file file with
    | Error d -> Some d
    | Ok u -> match elaborate u with
      | Error d -> Some d
      | Ok _ -> None in
  match diag with
  | Some d ->
    let sm = Cgen_utils.Source_map.create () in
    compare_outputs (file ^ ".err") (Cgen_utils.Diagnostic.to_string_with_source sm d)
  | None ->
    assert_failure @@ Format.sprintf
      "%s: expected the frontend to reject this input, but it succeeded" name

(* Elaborate an accepted program and golden the non-fatal warnings it
   accumulates, rendered with source excerpts. *)
let test_warn name _ =
  let file = ok name in
  match parse ~preprocess:false file with
  | Error d -> assert_failure @@ Cgen_utils.Diagnostic.to_string d
  | Ok u -> match elaborate u with
    | Error d -> assert_failure @@ Cgen_utils.Diagnostic.to_string d
    | Ok (_, []) ->
      assert_failure @@ Format.sprintf
        "%s: expected elaboration warnings, but none were produced" name
    | Ok (_, warnings) ->
      let sm = Cgen_utils.Source_map.create () in
      List.map warnings ~f:(Cgen_utils.Diagnostic.to_string_with_source sm)
      |> String.concat ~sep:"\n"
      |> compare_outputs (file ^ ".warn")

let lower_to_structured ?cpp file =
  let name = Filename.chop_extension (Filename.basename file) in
  match C.Parse.from_file ?cpp file with
  | Error d -> Context.fail (Cgen_utils.Diagnostic.to_error d)
  | Ok u -> match elaborate u with
    | Error d -> Context.fail (Cgen_utils.Diagnostic.to_error d)
    | Ok (t, _warnings) -> C.Lower.module_ ~name t

let from_c_abi ?cpp file =
  let open Context.Syntax in
  let* m = lower_to_structured ?cpp file in
  let* m = Passes.destructure m in
  let* tenv, m = Passes.initialize m in
  let* tenv, m = Passes.optimize tenv m in
  let* m = Passes.to_abi tenv m in
  Passes.optimize_abi ~invariants:true m

let test_sir name _ =
  let file = ok name in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.eval begin
    let open Context.Syntax in
    let+ m = lower_to_structured file in
    Format.asprintf "%a" Structured.Module.pp m
  end |> function
  | Ok s -> compare_outputs (file ^ ".sir") s
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

(* Run the platform-agnostic middle-end (through `Passes.optimize`) and
   dump the optimized Virtual IR. Used to show that the naive code the
   elaborator emits (slot-heavy, sometimes branchy) is cleaned up by the
   optimizer. *)
let test_opt name _ =
  let file = ok name in
  Context.init Machine.X86.Amd64_sysv.target |>
  Context.eval begin
    let open Context.Syntax in
    let* m = lower_to_structured file in
    let* m = Passes.destructure m in
    let* tenv, m = Passes.initialize m in
    let* _, m = Passes.optimize tenv m in
    let+ () =
      Virtual.Module.funs m |> Context.iter_seq_err ~f:Passes.Ssa.check in
    Format.asprintf "%a" Virtual.Module.pp m
  end |> function
  | Ok s -> compare_outputs (file ^ ".opt") s
  | Error err -> assert_failure @@ Format.asprintf "%a" Error.pp err

let test_native target abi ext name _ =
  let file = ok name in
  let driver = Format.sprintf "data/c/ok/%s.driver.%s.%s" name abi ext in
  let tmpname = Format.asprintf "cgen-c-%s-%s-%s" name abi ext in
  Native.run target
    ~asm:(Format.sprintf "/tmp/%s.S" tmpname)
    ~exe:(Format.sprintf "/tmp/%s" tmpname)
    ~driver_c:(driver ^ ".c")
    ~driver_output:(driver ^ ".output")
    ~build:(from_c_abi file)

let test_sysv_amd64_native = test_native Machine.X86.Amd64_sysv.target "sysv" "amd64"

(* Like {!test_native}, but preprocesses the input (like the `cgen` CLI does:
   `cpp -undef` plus the target's predefines), so `#include`-bearing whole
   programs — a hello world — compile and run. The `ok/<name>.c` file provides
   its own `main`; the driver is an empty placeholder the harness links. Only
   the program's stdout is golden'd (via the `.output` file), never the
   system-header-dependent IR. *)
let test_native_pp target abi ext name _ =
  let file = ok name in
  let cpp = C.Parse.Cpp.add_args C.Parse.Cpp.default (C.Predef.defines target) in
  let driver = Format.sprintf "data/c/ok/%s.driver.%s.%s" name abi ext in
  let tmpname = Format.asprintf "cgen-c-%s-%s-%s" name abi ext in
  Native.run target
    ~asm:(Format.sprintf "/tmp/%s.S" tmpname)
    ~exe:(Format.sprintf "/tmp/%s" tmpname)
    ~driver_c:(driver ^ ".c")
    ~driver_output:(driver ^ ".output")
    ~build:(from_c_abi ~cpp file)

let test_sysv_amd64_native_pp = test_native_pp Machine.X86.Amd64_sysv.target "sysv" "amd64"

let ok_case ?preprocess ?(sir = false) ?(opt = false) ?(warn = false) descr name =
  [ Format.sprintf "%s (parse)" descr >:: test_parse ?preprocess name
  ; Format.sprintf "%s (elab)" descr >:: test_elab ?preprocess name ]
  @ (if sir then [Format.sprintf "%s (sir)" descr >:: test_sir name] else [])
  @ (if opt then [Format.sprintf "%s (opt)" descr >:: test_opt name] else [])
  @ (if warn then [Format.sprintf "%s (warn)" descr >:: test_warn name] else [])

let ok_suite = "C frontend: accepted programs" >::: List.concat [
    ok_case ~sir:true "Declarator spiral rule" "declarators";
    ok_case "Typedefs and structs" "typedef_struct";
    ok_case ~sir:true "Enums" "enums";
    ok_case ~sir:true "Expression precedence" "expr";
    ok_case "Control flow" "control";
    ok_case ~sir:true "Functions and calls" "functions";
    ok_case ~sir:true "Main implicit return" "main_implicit_return";
    ok_case ~preprocess:true "Preprocessed input" "preprocessed";
    ok_case ~sir:true "Scalar arithmetic" "scalar";
    ok_case ~sir:true "Aggregates and arrays" "aggregate";
    ok_case ~sir:true "Switch statements" "switch";
    ok_case ~sir:true "Global initializers" "globals";
    ok_case ~sir:true "Bit fields" "bitfield";
    ok_case ~sir:true "Zero-width bit fields" "bitfield_zero";
    ok_case ~sir:true "Static bit-field initializers" "static_bitfield";
    ok_case ~sir:true "Block-scope statics" "static_local";
    ok_case ~sir:true "Variadic functions" "variadic";
    ok_case ~sir:true ~opt:true "Logic and control flow" "logic";
    ok_case ~sir:true ~opt:true "Loops and continue" "loops";
    ok_case ~opt:true "Nested-loop LICM variance" "nested_loop_licm";
    ok_case ~opt:true "Divisibility tests" "divisible";
    ok_case "Integer literal typing" "literals";
    ok_case ~sir:true "Function address-of" "funcaddr";
    ok_case ~sir:true "Nested designators" "designators";
    ok_case ~sir:true "Hexadecimal floating constants" "hexfloat";
    ok_case ~sir:true "Null pointer comparisons" "nullcmp";
    ok_case ~sir:true "Wide shifts with narrow counts" "shift";
    ok_case ~sir:true ~warn:true "Distinct pointer-type compare and assign" "ptr_distinct";
    ok_case ~sir:true "Discarded call results" "discard_call";
    ok_case ~sir:true "Block-scope shadowing" "scope_shadow";
    ok_case ~sir:true "Assignment expression value" "assign_value";
    ok_case ~sir:true ~opt:true "Duff's device" "duff";
    ok_case ~sir:true "Bit-field packing" "bitfield_pack";
    ok_case ~sir:true "Function-type typedefs" "func_typedef";
    ok_case ~sir:true "Incomplete/forward struct types" "incomplete_types";
    ok_case ~sir:true "Bit-counting builtins" "builtins";
    ok_case ~sir:true "Computed goto" "computed_goto";
    ok_case ~sir:true "Real-world C idioms" "c_idioms";
    ok_case ~sir:true "sizeof of a typedef-name" "sizeof_typedef";
    ok_case "Typedef-name parameter ambiguity" "param_typedef_paren";
  ]

let native_suite = "C frontend: native execution" >::: [
    (* AMD64 SysV *)
    "Scalar arithmetic (SysV AMD64)" >:: test_sysv_amd64_native "scalar";
    "Bit-counting builtins (SysV AMD64)" >:: test_sysv_amd64_native "builtins";
    "Computed goto (SysV AMD64)" >:: test_sysv_amd64_native "computed_goto";
    "Real-world C idioms (SysV AMD64)" >:: test_sysv_amd64_native "c_idioms";
    "Aggregates and arrays (SysV AMD64)" >:: test_sysv_amd64_native "aggregate";
    "Switch statements (SysV AMD64)" >:: test_sysv_amd64_native "switch";
    "Global initializers (SysV AMD64)" >:: test_sysv_amd64_native "globals";
    "Bit fields (SysV AMD64)" >:: test_sysv_amd64_native "bitfield";
    "Zero-width bit fields (SysV AMD64)" >:: test_sysv_amd64_native "bitfield_zero";
    "Static bit-field initializers (SysV AMD64)" >:: test_sysv_amd64_native "static_bitfield";
    "Block-scope statics (SysV AMD64)" >:: test_sysv_amd64_native "static_local";
    "Variadic functions (SysV AMD64)" >:: test_sysv_amd64_native "variadic";
    "Logic and control flow (SysV AMD64)" >:: test_sysv_amd64_native "logic";
    "Loops and continue (SysV AMD64)" >:: test_sysv_amd64_native "loops";
    "Divisibility tests (SysV AMD64)" >:: test_sysv_amd64_native "divisible";
    "Integer literal typing (SysV AMD64)" >:: test_sysv_amd64_native "literals";
    "Function address-of (SysV AMD64)" >:: test_sysv_amd64_native "funcaddr";
    "Nested designators (SysV AMD64)" >:: test_sysv_amd64_native "designators";
    "Hexadecimal floating constants (SysV AMD64)" >:: test_sysv_amd64_native "hexfloat";
    "Null pointer comparisons (SysV AMD64)" >:: test_sysv_amd64_native "nullcmp";
    "Wide shifts with narrow counts (SysV AMD64)" >:: test_sysv_amd64_native "shift";
    "Distinct pointer-type compare and assign (SysV AMD64)" >:: test_sysv_amd64_native "ptr_distinct";
    "Discarded call results (SysV AMD64)" >:: test_sysv_amd64_native "discard_call";
    "Block-scope shadowing (SysV AMD64)" >:: test_sysv_amd64_native "scope_shadow";
    "Assignment expression value (SysV AMD64)" >:: test_sysv_amd64_native "assign_value";
    "Duff's device (SysV AMD64)" >:: test_sysv_amd64_native "duff";
    "Bit-field packing (SysV AMD64)" >:: test_sysv_amd64_native "bitfield_pack";
    "Function-type typedefs (SysV AMD64)" >:: test_sysv_amd64_native "func_typedef";
    "Incomplete/forward struct types (SysV AMD64)" >:: test_sysv_amd64_native "incomplete_types";
    "Hello world (SysV AMD64)" >:: test_sysv_amd64_native_pp "hello";
  ]

let fail_suite = "C frontend: rejected programs" >::: [
    "Syntax error (return)" >:: test_error "syntax_return";
    "Undeclared identifier" >:: test_error "undeclared";
    "Incompatible redeclaration" >:: test_error "redeclaration";
    "Initializer type mismatch" >:: test_error "init_type";
    "String initializer too long" >:: test_error "string_too_long";
    "Non-constant static initializer" >:: test_error "static_init_nonconst";
    "Non-constant block static initializer" >:: test_error "static_local_nonconst";
    "Block extern with initializer" >:: test_error "extern_local_init";
    "va_start with undeclared last arg" >:: test_error "va_start_undeclared";
    "sizeof of a function" >:: test_error "sizeof_func";
    "assignment to a function" >:: test_error "assign_func";
    "address of an undeclared label" >:: test_error "labaddr_undeclared";
    "conflicting typedef redefinition" >:: test_error "typedef_conflict";
  ]

let () = run_test_tt_main @@ test_list [
    ok_suite;
    fail_suite;
    native_suite;
  ]
