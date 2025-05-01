open Core
open Regular.Std

type t = int

include Regular.Make(struct
    include Int
    let module_name = Some "Cgen.Egraph.Id"
    let version = "0.1"
  end)

module Tree = Patricia_tree.Make(struct
    include Int
    let size = Sys.int_size_in_bits
  end)

module Tree_set = Patricia_tree.Make_set(struct
    include Int
    let size = Sys.int_size_in_bits
  end)
