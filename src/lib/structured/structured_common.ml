type 'a ftree = 'a Ftree.t [@@deriving bin_io, sexp]

let compare_ftree compare t1 t2 = Ftree.compare t1 t2 ~compare
let equal_ftree equal t1 t2 = Ftree.equal t1 t2 ~equal
