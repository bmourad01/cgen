open Core
open Regular.Std

module T = struct
  type t = {
    name : string;
    bits : int;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let create ~name ~bits () = {name; bits}
let name t = t.name
let bits t = t.bits

include Regular.Make(struct
    include T
    let pp ppf t = Format.fprintf ppf "%s" t.name
    let version = "0.1"
    let hash = hash
    let module_name = Some "Cgen.Target"
  end)
