open Core
open Regular.Std

module T = struct
  type t = int [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pseudoentry = 0
let pseudoexit = 1
let is_pseudo l = l = pseudoentry || l = pseudoexit

let pp ppf l = Format.fprintf ppf "%%%08x" l
let pp_hum ppf l = Format.fprintf ppf ".L%x" l

include Regular.Make(struct
    include T
    let pp = pp
    let version = "0.1"
    let module_name = Some "Cabs.Label"
  end)
