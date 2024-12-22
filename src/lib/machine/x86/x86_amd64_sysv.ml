open X86_common
open X86_amd64_common

let target = Target.declare () ~name:"amd64-sysv" ~word ~little

module Machine = struct
  module Reg = Reg
  module Regvar = Regvar
  module Insn = Insn
  let lower_abi = Sysv.run
end

let () = Context.register_machine target (module Machine)
