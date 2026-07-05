open Core
module Regular = Cgen_utils.Regular

module T = struct
  type t = {
    section : string option;
    export  : bool;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pp ppf l =
  Option.iter l.section ~f:(Format.fprintf ppf "section \"%s\"");
  if l.export then begin
    if Option.is_some l.section then Format.fprintf ppf " ";
    Format.fprintf ppf "export"
  end

let create ?(section = None) ~export () = {section; export}

let section l = l.section
let export l = l.export

let default_export = {
  section = None;
  export = true;
}

let default_static = {
  section = None;
  export = false;
}

include Regular.Make(struct
    include T
    let pp = pp
  end)
