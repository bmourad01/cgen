open Core

module Regular = Cgen_utils.Regular
module C_data_model = Cgen_utils.C_data_model

module T = struct
  type t = {
    name       : string;
    little     : bool;
    data_model : C_data_model.t;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let targets = ref String.Map.empty

let enum_targets () =
  Map.to_sequence !targets |> Sequence.map ~f:snd

let declare ~name ~little ~data_model () =
  let t = {name; little; data_model} in
  match Map.add !targets ~key:name ~data:t with
  | `Duplicate -> failwithf "A target with the name %s already exists" name ()
  | `Ok m ->
    targets := m;
    t

let find name = Map.find !targets name

let name t = t.name

(* The native word/pointer size is the data model's pointer width. *)
let word t : Type.imm_base = match C_data_model.pointer_bits t.data_model with
  | 32 -> `i32
  | 64 -> `i64
  | n -> failwithf "Target %s has unsupported pointer width %d" t.name n ()

let bits t = Type.sizeof_imm_base (word t)
let little t = t.little
let data_model t = t.data_model

include Regular.Make(struct
    include T
    let pp ppf t = Format.fprintf ppf "%s" t.name
    let hash = hash
  end)
