open Core

module X86 = X86

let targets = [
  X86.Amd64_sysv.target;
]

let force_initialization () =
  Logs.debug (fun m -> m "forcing initialization of targets%!");
  ignore (Sys.opaque_identity targets)
