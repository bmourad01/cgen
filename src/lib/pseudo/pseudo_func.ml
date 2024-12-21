open Core

type 'a t = {
  name : string;
  blks : 'a Pseudo_blk.t Ftree.t;
} [@@deriving sexp]

let create ~name ~blks = {
  name;
  blks = Ftree.of_list blks;
}

let name t = t.name
let blks ?(rev = false) t = Ftree.enum ~rev t.blks
