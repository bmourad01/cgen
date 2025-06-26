open Core
open X86_common
open X86_amd64_common

let target = Target.declare () ~name:"amd64-sysv" ~word ~little

let clobbered_map = X86_amd64_regalloc.Typed_writes.rmap' [
    `rax,   `i64;
    `rcx,   `i64;
    `rdx,   `i64;
    `rdi,   `i64;
    `rsi,   `i64;
    `rsp,   `i64;
    `r8,    `i64;
    `r9,    `i64;
    `r10,   `i64;
    `r11,   `i64;
    `xmm0,  `v128;
    `xmm1,  `v128;
    `xmm2,  `v128;
    `xmm3,  `v128;
    `xmm4,  `v128;
    `xmm5,  `v128;
    `xmm6,  `v128;
    `xmm7,  `v128;
    `xmm8,  `v128;
    `xmm9,  `v128;
    `xmm10, `v128;
    `xmm11, `v128;
    `xmm12, `v128;
    `xmm13, `v128;
    `xmm14, `v128;
    `xmm15, `v128;
  ]

(* Conservative set of registers that will be clobbered by a
   function call. *)
let clobbered =
  Regvar.Set.of_list @@
  List.map ~f:fst @@
  Map.to_alist clobbered_map

module Machine = struct
  let target = target

  let call_args_stack_size sz = (sz + 15) land (-16)
  let stack_args_offset = 16
  let supports_uitof = false

  module Reg = struct
    include Reg

    let allocatable = [
      `rax;
      `rcx;
      `rdx;
      `rsi;
      `rdi;
      `r8;
      `r9;
      `r10;
      `r11;
      `rbx;
      `r12;
      `r13;
      `r14;
      `r15;
    ]

    let allocatable_fp = [
      `xmm0;
      `xmm1;
      `xmm2;
      `xmm3;
      `xmm4;
      `xmm5;
      `xmm6;
      `xmm7;
      `xmm8;
      `xmm9;
      `xmm10;
      `xmm11;
      `xmm12;
      `xmm13;
      `xmm14;
      `xmm15;
    ]

    let is_callee_save = function
      | `rbx
      | `r12
      | `r13
      | `r14
      | `r15 -> true
      | _ -> false

    let is_arg = function
      | `rdi
      | `rsi
      | `rdx
      | `rcx
      | `r8
      | `r9
      | `xmm0
      | `xmm1
      | `xmm2
      | `xmm3
      | `xmm4
      | `xmm5
      | `xmm6
      | `xmm7 -> true
      | _ -> false
  end

  module Regvar = Regvar

  module Insn = struct
    include Insn
    let writes = writes clobbered
  end

  module Lower_abi = Sysv.Make
  module Isel = X86_amd64_isel.Make

  module Regalloc = struct
    include X86_amd64_regalloc
    let writes_with_types = writes_with_types clobbered_map
  end

  module Peephole = X86_amd64_peephole
  module Emit = X86_amd64_emit
end

let () = Context.register_machine target (module Machine)
