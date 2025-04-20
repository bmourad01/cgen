open Core

include Context_common

module Var = Context_var
module Label = Context_label
module Local = Context_local

module Virtual = struct
  include Context_virtual
  module Module = Context_virtual_module
  module Abi = Context_virtual_abi
end

let init target = {
  target;
  nextvar = Int63.zero;
  nextlabel = Label.init;
}

include M

let init_ctx s = {
  state = s;
  local = Dict.empty;
}

let reject err = Error err

let run x s =
  x.run (init_ctx s) ~reject ~accept:(fun x s -> Ok (x, s.state))

let eval x s =
  x.run (init_ctx s) ~reject ~accept:(fun x _ -> Ok x)

let register_machine = Context_machine.register
let init_machines = Context_machine.init_machines
let machine = Context_machine.machine
