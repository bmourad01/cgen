open Core
open X86_common
open X86_amd64_common

let target = Target.declare () ~name:"amd64-sysv" ~word ~little

(* Conservative set of registers that will be clobbered by a
   function call. *)
let clobbered =
  Regvar.Set.of_list @@
  List.map ~f:Regvar.reg [
    `rax;
    `rcx;
    `rdx;
    `rdi;
    `rsi;
    `rsp;
    `r8;
    `r9;
    `r10;
    `r11;
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

module Machine = struct
  let target = target

  let call_args_stack_size sz = (sz + 15) land (-16)

  module Reg = Reg
  module Regvar = Regvar

  module Insn = struct
    include Insn
    let reads = reads clobbered
    let writes = writes clobbered
  end

  module Isel = X86_amd64_isel.Make

  let lower_abi = Sysv.run
end

let () = Context.register_machine target (module Machine)
