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

let targets = ref String.Map.empty

let enum_targets () =
  Map.to_sequence !targets |> Seq.map ~f:snd

let declare ~name ~word ~little () =
  let t = {name; word; little} in
  match Map.add !targets ~key:name ~data:t with
  | `Duplicate -> failwithf "A target with the name %s already exists" name ()
  | `Ok m ->
    targets := m;
    t

let name t = t.name
let word t = t.word
let bits t = Type.sizeof_imm_base t.word
let little t = t.little

include Regular.Make(struct
    include T
    let pp ppf t = Format.fprintf ppf "%s" t.name
    let version = "0.1"
    let hash = hash
    let module_name = Some "Cgen.Target"
  end)
