open Core

module type S = Machine_intf.S
  with type 'a context := 'a Context_common.t

let targets = Hashtbl.create (module Target)

let register t ((module M : S) as m) =
  match Hashtbl.add targets ~key:t ~data:m with
  | `Ok -> ()
  | `Duplicate ->
    invalid_argf "Target %a already exists" Target.pps t ()

let get t = Hashtbl.find targets t
