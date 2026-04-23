open Core
open Context_common

let targets = String.Table.create ()
let get t = Hashtbl.find targets @@ Target.name t

let register ((module M : Machine_intf.S) as data) =
  let key = Target.name M.target in
  match Hashtbl.add targets ~key ~data with
  | `Duplicate ->
    invalid_argf "Target %s is already registered to a machine" key ()
  | `Ok -> ()

let machine = {
  M.run = fun ~reject ~accept s -> match get s.state.target with
    | None -> reject @@ Error.createf
        "%s: machine for target %a is not registered"
        error_prefix Target.pps s.state.target
    | Some m -> accept m s
}
