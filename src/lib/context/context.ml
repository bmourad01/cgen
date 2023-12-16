open Core

include Context_state

type var = Var.t
type label = Label.t

module Var = Context_var
module Label = Context_label

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

let reject err = Error err
let run x s = x.run s ~reject ~accept:(fun x s -> Ok (x, s))
let eval x s = x.run s ~reject ~accept:(fun x _ -> Ok x)

module type Machine = Context_machine.Machine

let register_machine = Context_machine.register

let machine =
  let* t = target in
  match Context_machine.get t with
  | Some m -> !!m
  | None ->
    failf "Machine for target %a is not registered"
      Target.pp t ()
