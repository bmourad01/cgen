(* Infer the interval constraints from a comparison op. *)

open Core
open Virtual
open Sccp_intervals_common

(* Constrain `y` to `i` in relation to the condition `x`,
   overwriting the previous constraint if it is present. *)
let set_constraint ctx x y i = match (y : operand) with
  | `var y ->
    let i = Lazy.force i in
    Hashtbl.update ctx.cond x ~f:(function
        | None -> Var.Map.singleton y i
        | Some s -> update s y i)
  | _ -> ()

(* If the interval we're comparing against isn't singular,
   then we could underapproximate the value we're comparing.

   Say we have `%c = lt.w %a, %b`, where %a has the interval
   [0, 10):32 and %b has the interval [5, 20):32.

   Since %a and %b, intersect, we can't simply constrain %a to
   be [0, 5):32, because it is possible that %a could be in the
   interval [5, 10):32, which could satisfy the condition in a
   possible run of the program. If, on the other hand, %b was
   the single constant 5, then this would be a sound approximation.

   The solution should be to leave %a untouched, which we use
   the full interval for (this constraint is discarded later).
*)
let cmp p i = lazy begin
  if I.is_single i
  then I.satisfying_icmp_region i p
  else I.create_full ~size:(I.size i)
end

let eq  a b = cmp EQ  b, cmp EQ  a
let ne  a b = cmp NE  b, cmp NE  a
let lt  a b = cmp LT  b, cmp GT  a
let le  a b = cmp LE  b, cmp GE  a
let gt  a b = cmp GT  b, cmp LT  a
let ge  a b = cmp GE  b, cmp LE  a
let slt a b = cmp SLT b, cmp SGT a
let sle a b = cmp SLE b, cmp SGE a
let sgt a b = cmp SGT b, cmp SLT a
let sge a b = cmp SGE b, cmp SLE a
