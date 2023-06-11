open Core
open Regular.Std

type t = int

include Regular.Make(struct
    include Int
    let module_name = Some "Cgen.E2.Id"
    let version = "0.1"
  end)
