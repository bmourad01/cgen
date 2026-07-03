open Core

module Dm = Cgen_utils.C_data_model
module Target = Cgen.Target

let signed_max ~bytes ~suffix =
  let b = Buffer.create 64 in
  Buffer.add_string b "0x7f";
  for _ = 1 to bytes - 1 do Buffer.add_string b "ff" done;
  Buffer.add_string b suffix;
  Buffer.contents b

let is_amd64 name =
  String.is_prefix name ~prefix:"amd64" ||
  String.is_prefix name ~prefix:"x86_64"

(* Architecture object-macros, keyed off the target name. *)
let arch_macros target = match Target.name target with
  | name when is_amd64 name ->
    ["__x86_64__"; "__amd64__"]
  | _ -> []

(* Operating-system object-macros for the host.

   Preprocessing reads the host's system headers, so their OS identity must
   match the host (separate from cgen's `Target.t` abstraction).

   Here, we'll ask the OCaml `Sys` module what OS it was configured for.
*)
let os_macros () = match Stdlib.Sys.os_type with
  | "Unix" when Stdlib.Sys.file_exists "/proc/version" ->
    ["__unix__"; "__linux__"; "__gnu_linux__"]
  | "Unix" when Stdlib.Sys.file_exists "/System/Library/CoreServices/SystemVersion.plist" ->
    ["__unix__"; "__APPLE__"; "__MACH__"]
  | "Unix" -> ["__unix__"]
  | _ -> []

let defines target =
  let dm = Target.data_model target in
  let short_b = Dm.short_bytes in
  let int_b = Dm.int_bytes dm in
  let long_b = Dm.long_bytes dm in
  let llong_b = Dm.long_long_bytes in
  let ptr_b = Dm.pointer_bytes dm in
  let obj name = Format.sprintf "-D%s" name in
  let def name value = Format.sprintf "-D%s=%s" name value in
  let c_int_type ~bytes ~signed =
    if bytes = Dm.char_bytes then (if signed then "signed char" else "unsigned char")
    else if bytes = short_b then (if signed then "short int" else "short unsigned int")
    else if bytes = int_b then (if signed then "int" else "unsigned int")
    else if bytes = long_b then (if signed then "long int" else "long unsigned int")
    else (if signed then "long long int" else "long long unsigned int") in
  List.concat [
    (* Standard features cgen does not implement. *)
    List.map ~f:obj [
      "__STDC_NO_ATOMICS__";
      "__STDC_NO_COMPLEX__";
      "__STDC_NO_THREADS__";
      "__STDC_NO_VLA__";
    ];
    (* Neutralize the GNU `__extension__` marker (a no-op qualifier). *)
    [def "__extension__" ""];
    (* Byte order. *)
    [ def "__ORDER_LITTLE_ENDIAN__" "1234";
      def "__ORDER_BIG_ENDIAN__" "4321";
      def "__BYTE_ORDER__"
        (if Target.little target
         then "__ORDER_LITTLE_ENDIAN__" else "__ORDER_BIG_ENDIAN__");
      def "__FLT_EVAL_METHOD__" "0" ];
    (* Type sizes, in bytes. *)
    [ def "__CHAR_BIT__" (Int.to_string Dm.char_bits);
      def "__SIZEOF_SHORT__" (Int.to_string short_b);
      def "__SIZEOF_INT__" (Int.to_string int_b);
      def "__SIZEOF_LONG__" (Int.to_string long_b);
      def "__SIZEOF_LONG_LONG__" (Int.to_string llong_b);
      def "__SIZEOF_POINTER__" (Int.to_string ptr_b);
      def "__SIZEOF_SIZE_T__" (Int.to_string ptr_b);
      def "__SIZEOF_PTRDIFF_T__" (Int.to_string ptr_b);
      def "__SIZEOF_FLOAT__" (Int.to_string Dm.float_bytes);
      def "__SIZEOF_DOUBLE__" (Int.to_string Dm.double_bytes);
      def "__SIZEOF_WCHAR_T__" "4" ];
    (* Type maxima (gcc's <limits.h> and portable code consult these). *)
    [ def "__SCHAR_MAX__" (signed_max ~bytes:1 ~suffix:"");
      def "__SHRT_MAX__" (signed_max ~bytes:short_b ~suffix:"");
      def "__INT_MAX__" (signed_max ~bytes:int_b ~suffix:"");
      def "__LONG_MAX__" (signed_max ~bytes:long_b ~suffix:"L");
      def "__LONG_LONG_MAX__" (signed_max ~bytes:llong_b ~suffix:"LL") ];
    (* Compiler implementation types the freestanding headers rely on. These
       are compiler builtins that `-undef` strips on some gcc versions (which
       is why, for example, a real <stdio.h> can fail to resolve `size_t`), so
       define them explicitly. *)
    [ def "__SIZE_TYPE__" (c_int_type ~bytes:ptr_b ~signed:false);
      def "__PTRDIFF_TYPE__" (c_int_type ~bytes:ptr_b ~signed:true);
      def "__INTPTR_TYPE__" (c_int_type ~bytes:ptr_b ~signed:true);
      def "__UINTPTR_TYPE__" (c_int_type ~bytes:ptr_b ~signed:false);
      def "__INTMAX_TYPE__" (c_int_type ~bytes:long_b ~signed:true);
      def "__UINTMAX_TYPE__" (c_int_type ~bytes:long_b ~signed:false);
      def "__WCHAR_TYPE__" (c_int_type ~bytes:int_b ~signed:true);
      def "__WINT_TYPE__" (c_int_type ~bytes:int_b ~signed:false);
      def "__SIG_ATOMIC_TYPE__" (c_int_type ~bytes:int_b ~signed:true);
      def "__CHAR16_TYPE__" (c_int_type ~bytes:short_b ~signed:false);
      def "__CHAR32_TYPE__" (c_int_type ~bytes:int_b ~signed:false) ];
    (* Plain `char` signedness (only the unsigned case needs a macro). *)
    (if Dm.char_signed dm then [] else [obj "__CHAR_UNSIGNED__"]);
    (* Data model. *)
    (match Dm.model dm with
     | Dm.LP64 -> [obj "__LP64__"; obj "_LP64"]
     | Dm.LP32 | Dm.ILP32 | Dm.LLP64 | Dm.ILP64 -> []);
    (* Architecture and (host) operating system. *)
    List.map ~f:obj (arch_macros target);
    List.map ~f:obj (os_macros ());
  ]
