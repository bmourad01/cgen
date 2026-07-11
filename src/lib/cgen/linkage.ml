open Core
module Regular = Cgen_utils.Regular

type visibility =
  | Default
  | Hidden
  | Internal
  | Protected
[@@deriving bin_io, compare, equal, hash, sexp]

module T = struct
  type t = {
    section    : string option;
    export     : bool;
    weak       : bool;
    visibility : visibility;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let string_of_visibility = function
  | Default -> "default" | Hidden -> "hidden"
  | Internal -> "internal" | Protected -> "protected"

let pp ppf l =
  let sep = ref false in
  let item f =
    if !sep then Format.fprintf ppf " ";
    sep := true;
    f () in
  Option.iter l.section ~f:(fun s ->
      item (fun () -> Format.fprintf ppf "section \"%s\"" s));
  if l.export then item (fun () -> Format.fprintf ppf "export");
  if l.weak then item (fun () -> Format.fprintf ppf "weak");
  match l.visibility with
  | Default -> ()
  | v -> item (fun () -> Format.fprintf ppf "visibility %s" (string_of_visibility v))

let create
    ?(section = None)
    ?(weak = false)
    ?(visibility = Default)
    ~export
    () =
  {section; export; weak; visibility}

let section l = l.section
let export l = l.export
let weak l = l.weak
let visibility l = l.visibility

let default_export = {
  section = None;
  export = true;
  weak = false;
  visibility = Default;
}

let default_static = {
  section = None;
  export = false;
  weak = false;
  visibility = Default;
}

include Regular.Make(struct
    include T
    let pp = pp
  end)
