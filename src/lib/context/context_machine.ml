open Core

module type S = Machine_intf.S
  with type 'a context := 'a Context_common.t

let targets = String.Table.create ()

let register t ((module M : S) as m) =
  match Hashtbl.add targets ~key:(Target.name t) ~data:m with
  | `Ok -> ()
  | `Duplicate ->
    invalid_argf "Target %a already exists" Target.pps t ()

let get t = Hashtbl.find targets @@ Target.name t
