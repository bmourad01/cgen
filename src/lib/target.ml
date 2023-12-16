open Core
open Regular.Std

module T = struct
  type t = {
    name   : string;
    word   : Type.imm_base;
    little : bool;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let create ~name ~word ~little () = {name; word; little}
let name t = t.name
let word t = t.word
let bits t = Type.sizeof_imm_base t.word
let little t = t.little

include Regular.Make(struct
    include T

    let pp ppf t =
      Format.fprintf ppf "%s:%d:%s"
        t.name (Type.sizeof_imm_base t.word)
        (if t.little then "le" else "be")

    let version = "0.1"
    let hash = hash
    let module_name = Some "Cgen.Target"
  end)
