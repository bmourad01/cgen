(* Try to infer the boolean result of a comparison op. *)

module I = Bv_interval

let bool_eq a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean Bv.(a = b)
  | _ when I.(is_empty @@ intersect a b) -> I.boolean_false
  | _ -> I.boolean_full

let bool_ne a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean Bv.(a <> b)
  | _ when I.(is_empty @@ intersect a b) -> I.boolean_true
  | _ -> I.boolean_full

let umin = I.unsigned_min
let umax = I.unsigned_max

let less f a b =
  if f (umax a) (umin b) then I.boolean_true
  else if not (f (umin a) (umax b)) then I.boolean_false
  else I.boolean_full

let greater f a b =
  if f (umin a) (umax b) then I.boolean_true
  else if not (f (umax a) (umin b)) then I.boolean_false
  else I.boolean_full

let bool_lt a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean Bv.(a < b)
  | _ -> less Bv.(<) a b

let bool_le a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean Bv.(a <= b)
  | _ -> less Bv.(<=) a b

let bool_gt a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean Bv.(a > b)
  | _ -> greater Bv.(>) a b

let bool_ge a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean Bv.(a >= b)
  | _ -> greater Bv.(>=) a b

let scmp t a b = Bv.(signed_compare a b @@ modulus @@ Type.sizeof_imm t)

let scmplt t a b = scmp t a b <  0
let scmple t a b = scmp t a b <= 0
let scmpgt t a b = scmp t a b >  0
let scmpge t a b = scmp t a b >= 0

let smin = I.signed_min
let smax = I.signed_max

let sless f a b =
  if f (smax a) (smin b) then I.boolean_true
  else if not (f (smin a) (smax b)) then I.boolean_false
  else I.boolean_full

let sgreater f a b =
  if f (smin a) (smax b) then I.boolean_true
  else if not (f (smax a) (smin b)) then I.boolean_false
  else I.boolean_full

let bool_slt t a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean @@ scmplt t a b
  | _ -> sless (scmplt t) a b

let bool_sle t a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean @@ scmple t a b
  | _ -> sless (scmple t) a b

let bool_sgt t a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean @@ scmpgt t a b
  | _ -> sgreater (scmpgt t) a b

let bool_sge t a b = match I.(single_of a, single_of b) with
  | Some a, Some b -> I.boolean @@ scmpge t a b
  | _ -> sgreater (scmpge t) a b
