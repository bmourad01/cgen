type 'a t = {
  label : Label.t;
  insns : 'a Ftree.t;
} [@@deriving sexp]

let create ~label ~insns = {
  label;
  insns = Ftree.of_list insns
}

let label t = t.label
let insns ?(rev = false) t = Ftree.enum ~rev t.insns
