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

let eq a b =
  lazy I.(inverse @@ allowed_icmp_region b NE),
  lazy I.(inverse @@ allowed_icmp_region a NE)

let ne a b =
  lazy I.(inverse @@ allowed_icmp_region b EQ),
  lazy I.(inverse @@ allowed_icmp_region a EQ)

let lt a b =
  lazy I.(inverse @@ allowed_icmp_region b GE),
  lazy I.(inverse @@ allowed_icmp_region a LE)

let le a b =
  lazy I.(inverse @@ allowed_icmp_region b GT),
  lazy I.(inverse @@ allowed_icmp_region a LT)

let gt a b =
  lazy I.(inverse @@ allowed_icmp_region b LE),
  lazy I.(inverse @@ allowed_icmp_region a GE)

let ge a b =
  lazy I.(inverse @@ allowed_icmp_region b LT),
  lazy I.(inverse @@ allowed_icmp_region a GT)

let slt a b =
  lazy I.(inverse @@ allowed_icmp_region b SGE),
  lazy I.(inverse @@ allowed_icmp_region a SLE)

let sle a b =
  lazy I.(inverse @@ allowed_icmp_region b SGT),
  lazy I.(inverse @@ allowed_icmp_region a SLT)

let sgt a b =
  lazy I.(inverse @@ allowed_icmp_region b SLE),
  lazy I.(inverse @@ allowed_icmp_region a SGE)

let sge a b =
  lazy I.(inverse @@ allowed_icmp_region b SLT),
  lazy I.(inverse @@ allowed_icmp_region a SGT)
