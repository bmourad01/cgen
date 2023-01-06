open Core
open Regular.Std

module T = struct
  type t = Int63.t [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pseudoentry = Int63.of_int 0
let pseudoexit = Int63.of_int 1
let is_pseudo l = Int63.(l = pseudoentry || l = pseudoexit)

let pp ppf l = Format.fprintf ppf "%%%08Lx" @@ Int63.to_int64 l
let pp_hum ppf l = Format.fprintf ppf ".L%Lx" @@ Int63.to_int64 l

include Regular.Make(struct
    include T
    let pp = pp
    let version = "0.1"
    let module_name = Some "Cabs.Label"
  end)
