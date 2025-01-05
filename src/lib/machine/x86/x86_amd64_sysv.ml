open X86_common
open X86_amd64_common

let target = Target.declare () ~name:"amd64-sysv" ~word ~little

module Machine = struct
  let target = target
  module Reg = Reg
  module Regvar = Regvar
  module Insn = Insn
  module Isel = X86_amd64_isel.Make
  let lower_abi = Sysv.run
end

let () = Context.register_machine target (module Machine)
