open Core
open Regular.Std

module T = struct
  type t = {
    name : string;
    word : Type.imm_base;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let create ~name ~word () = {name; word}
let name t = t.name
let word t = t.word
let bits t = Type.sizeof_imm_base t.word

include Regular.Make(struct
    include T
    let pp ppf t = Format.fprintf ppf "%s" t.name
    let version = "0.1"
    let hash = hash
    let module_name = Some "Cgen.Target"
  end)
