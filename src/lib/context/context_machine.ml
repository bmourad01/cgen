open Core
open Context_state

module type Machine = sig
  val lower_abi : Typecheck.env -> Virtual.func -> Virtual.Abi.func t
end

let targets : (Target.t, (module Machine)) Hashtbl.t =
  Hashtbl.create (module Target)

let register t ((module M : Machine) as m) =
  match Hashtbl.add targets ~key:t ~data:m with
  | `Ok -> ()
  | `Duplicate ->
    invalid_argf "Target %a already exists" Target.pps t ()

let get t = Hashtbl.find targets t
